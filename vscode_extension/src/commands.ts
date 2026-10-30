import * as vscode from "vscode";
import {
  analyzeReport,
  assertNever,
  BackendOptions,
  BackendRun,
  DEFAULT_DAFNY_COMMAND,
  RunStatus,
  SolverKind,
  VerifierBackend,
  VerifierId,
} from "@proofpulse/core";
import { getDafnyPath, getDecorationOpacity, getShowImplicitChecks, getForceMinimization, getNoAbstractInterpretation, getSolverPath, getTimeout, getZ3Path } from "./config";
import { backendForDocument, backendForPath, supportedExtensionsLabel } from "./backends";
import { applyDecorations } from "./decorations";
import { startNewSession, isSessionCurrent } from "./run-session";
import { writeCache, invalidateCache } from "./result-cache";

let outputChannel: vscode.OutputChannel | undefined;
let statusBarItem: vscode.StatusBarItem | undefined;

function getOutputChannel(): vscode.OutputChannel {
  if (!outputChannel) {
    outputChannel = vscode.window.createOutputChannel("ProofPulse");
  }
  return outputChannel;
}

function logInfo(msg: string): void {
  const ch = getOutputChannel();
  ch.appendLine(`[${new Date().toISOString()}] ${msg}`);
}

function getStatusBarItem(): vscode.StatusBarItem {
  if (!statusBarItem) {
    statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 0);
  }
  return statusBarItem;
}

function showStatusBar(text: string): void {
  const item = getStatusBarItem();
  item.text = `$(beaker) ProofPulse: ${text}`;
  item.show();
}

function hideStatusBar(): void {
  if (statusBarItem) {
    statusBarItem.hide();
  }
}

/** Options for a backend run, from the user's settings. */
function backendOptions(backend: VerifierBackend, context: vscode.ExtensionContext): BackendOptions {
  const solverPath = getSolverPath();
  const minimizationSolverPath = getZ3Path() || undefined;
  return {
    toolPath: getDafnyPath(context),
    timeoutSeconds: getTimeout(),
    ...(solverPath ? { solver: { kind: SolverKind.Z3, path: solverPath } } : {}),
    ...(getForceMinimization()
      ? { minimization: minimizationSolverPath ? { solver: { kind: SolverKind.Z3, path: minimizationSolverPath } } : {} }
      : {}),
    ...(backend.id === VerifierId.Dafny
      ? { backendOptions: { backend: VerifierId.Dafny, noAbstractInterpretation: getNoAbstractInterpretation() } }
      : {}),
  };
}

export async function runAnalysis(editor: vscode.TextEditor, context: vscode.ExtensionContext): Promise<void> {
  const filePath = editor.document.fileName;
  const sourceCode = editor.document.getText();
  const forceMin = getForceMinimization();
  const backend = backendForDocument(editor.document);
  if (!backend) return;

  const session = startNewSession(filePath);

  // Invalidate existing cache for this file (source changed)
  invalidateCache(filePath).catch(() => {});

  logInfo(`Running ${backend.displayName} analysis on ${filePath} (forceMinimization=${forceMin}, session=${session.id})`);
  showStatusBar(`${backend.displayName} — Running...`);

  await vscode.window.withProgress(
    { location: vscode.ProgressLocation.Notification, title: "ProofPulse: Running analysis…", cancellable: false },
    async () => {
      try {
        const options = backendOptions(backend, context);
        const dafnyPath = options.toolPath ?? DEFAULT_DAFNY_COMMAND;
        const timeout = options.timeoutSeconds ?? getTimeout();
        logInfo(`toolPath=${dafnyPath}, timeout=${timeout}`);

        const result: BackendRun = await backend.run(filePath, {
          ...options,
          onWarning: (msg) => logInfo(msg),
          signal: session.abortController.signal,
          onPreliminaryResult: (prelim) => {
            if (!isSessionCurrent(session) || prelim.status !== RunStatus.Completed || !prelim.report) return;
            const proof = analyzeReport(sourceCode, prelim.report);
            applyDecorations(editor, proof.proofGraph.getAllNodes(), getDecorationOpacity(), getShowImplicitChecks());
            logInfo(`Applied preliminary decorations: ${proof.lineStatus.length} lines`);
            showStatusBar(`${backend.displayName} — Preliminary ✓ — Minimizing...`);
          },
        });

        if (!isSessionCurrent(session)) {
          logInfo(`Session ${session.id} no longer current, discarding results`);
          hideStatusBar();
          return;
        }

        const rawLog = result.rawLog ?? "";
        logInfo(`${backend.displayName} exited ${result.exitCode}, status=${result.status}, error=${result.errorMessage ?? "none"}, logLen=${rawLog.length}`);

        switch (result.status) {
          case RunStatus.Completed:
            break;
          case RunStatus.Aborted:
            logInfo(`Session ${session.id} was aborted, silently discarding`);
            hideStatusBar();
            return;
          case RunStatus.Failed: {
            hideStatusBar();
            const ch = getOutputChannel();
            ch.appendLine(`--- ERROR ---\n${result.errorMessage}\n---`);
            ch.show(true);
            vscode.window.showErrorMessage(
              `ProofPulse: analysis failed. See Output → ProofPulse for details.`,
            );
            return;
          }
          case RunStatus.TimedOut:
            hideStatusBar();
            vscode.window.showWarningMessage("ProofPulse: analysis timed out.");
            return;
          default:
            assertNever(result.status, "run status");
        }

        const proof = analyzeReport(sourceCode, result.report!);
        applyDecorations(editor, proof.proofGraph.getAllNodes(), getDecorationOpacity(), getShowImplicitChecks());
        logInfo(`Applied decorations: ${proof.lineStatus.length} lines`);
        hideStatusBar();

        // Write cache on successful completion
        try {
          const cmdParts = [dafnyPath, "verify", filePath,
            "--verification-time-limit", String(timeout),
            ...(forceMin ? ["--solver-path", "<wrapper>"] : []),
            ...(getNoAbstractInterpretation() ? ["--no-abstract-interpretation"] : []),
          ];
          const command = cmdParts.map(p => p.includes(" ") ? `"${p}"` : p).join(" ");
          await writeCache(filePath, sourceCode, rawLog, forceMin, command);
          logInfo(`Cache written for ${filePath}`);
        } catch (cacheErr: unknown) {
          const cacheMsg = cacheErr instanceof Error ? cacheErr.message : String(cacheErr);
          logInfo(`WARNING: cache write failed: ${cacheMsg}`);
        }
      } catch (err: unknown) {
        hideStatusBar();
        if (!isSessionCurrent(session)) return;
        const msg = err instanceof Error ? err.message : String(err);
        logInfo(`Exception: ${msg}`);
        const ch = getOutputChannel();
        ch.appendLine(`--- EXCEPTION ---\n${msg}\n---`);
        ch.show(true);
        vscode.window.showErrorMessage(`ProofPulse: ${msg}`);
      }
    },
  );
}

export function registerRunAnalysis(context: vscode.ExtensionContext): void {
  const disposable = vscode.commands.registerCommand("proofpulse.runAnalysis", async () => {
    const editor = vscode.window.activeTextEditor;
    if (!editor || !backendForDocument(editor.document)) {
      vscode.window.showWarningMessage(`ProofPulse: Open a ${supportedExtensionsLabel()} file first.`);
      return;
    }
    await runAnalysis(editor, context);
  });

  context.subscriptions.push(disposable);
}

export function registerGetProofReport(context: vscode.ExtensionContext): void {
  const disposable = vscode.commands.registerCommand(
    "proofpulse.getProofReport",
    async (uri?: vscode.Uri) => {
      const filePath =
        uri?.fsPath ?? vscode.window.activeTextEditor?.document.fileName;

      if (!filePath || !backendForPath(filePath)) {
        vscode.window.showWarningMessage(`ProofPulse: Select a ${supportedExtensionsLabel()} file.`);
        return;
      }

      try {
        const { spawn } = await import("node:child_process");
        const serverScript = vscode.Uri.joinPath(
          context.extensionUri,
          "dist",
          "web_viewer",
          "server.js",
        ).fsPath;

        const child = spawn(process.execPath, [serverScript, "--file", filePath,
          ...(getDafnyPath(context) !== DEFAULT_DAFNY_COMMAND ? ["--dafny-path", getDafnyPath(context)] : []),
          ...(getTimeout() !== 60 ? ["--timeout", String(getTimeout())] : []),
          ...(getForceMinimization() ? ["--force-minimization"] : []),
          ...(getNoAbstractInterpretation() ? ["--no-abstract-interpretation"] : []),
        ], {
          stdio: "pipe",
          detached: true,
        });

        child.unref();

        // Wait for server to print its URL, then open in browser
        child.stdout?.on("data", (data: Buffer) => {
          const output = data.toString();
          const match = output.match(/http:\/\/localhost:\d+/);
          if (match) {
            vscode.env.openExternal(vscode.Uri.parse(match[0]));
          }
        });

        child.stderr?.on("data", (data: Buffer) => {
          const text = data.toString().trim();
          // Ignore Node.js runtime warnings (e.g. MODULE_TYPELESS_PACKAGE_JSON)
          if (!text || text.startsWith("(node:")) return;
          vscode.window.showErrorMessage(
            `ProofPulse: ${text}`,
          );
        });

        child.on("error", (err: Error) => {
          vscode.window.showErrorMessage(
            `ProofPulse: Failed to start viewer — ${err.message}`,
          );
        });
      } catch (err: unknown) {
        const msg = err instanceof Error ? err.message : String(err);
        vscode.window.showErrorMessage(
          `ProofPulse: Failed to launch proof report — ${msg}`,
        );
      }
    },
  );

  context.subscriptions.push(disposable);
}
