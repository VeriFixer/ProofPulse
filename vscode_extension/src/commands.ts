import * as vscode from "vscode";
import { runDafny, parseProof } from "@proofpulse/core";
import { getDafnyPath, getDecorationOpacity, getForceMinimization, getTimeout } from "./config";
import { applyDecorations } from "./decorations";

export async function runAnalysis(editor: vscode.TextEditor, context: vscode.ExtensionContext): Promise<void> {
  const filePath = editor.document.fileName;
  const sourceCode = editor.document.getText();

  await vscode.window.withProgress(
    { location: vscode.ProgressLocation.Notification, title: "ProofPulse: Running analysis…", cancellable: false },
    async () => {
      try {
        const result = await runDafny(filePath, {
          dafnyPath: getDafnyPath(),
          timeoutSeconds: getTimeout(),
          forceMinimization: getForceMinimization(),
        });

        if (result.error) {
          vscode.window.showErrorMessage(`ProofPulse: ${result.error}`);
          return;
        }

        const proof = parseProof(sourceCode, result.log);
        applyDecorations(editor, proof.lineStatus, proof.proofGraph.getAllNodes(), getDecorationOpacity(), context.extensionPath);
      } catch (err: unknown) {
        const msg = err instanceof Error ? err.message : String(err);
        vscode.window.showErrorMessage(`ProofPulse: ${msg}`);
      }
    },
  );
}

export function registerRunAnalysis(context: vscode.ExtensionContext): void {
  const disposable = vscode.commands.registerCommand("proofpulse.runAnalysis", async () => {
    const editor = vscode.window.activeTextEditor;
    if (!editor || !editor.document.fileName.endsWith(".dfy")) {
      vscode.window.showWarningMessage("ProofPulse: Open a .dfy file first.");
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

      if (!filePath || !filePath.endsWith(".dfy")) {
        vscode.window.showWarningMessage("ProofPulse: Select a .dfy file.");
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

        const child = spawn("node", [serverScript, "--file", filePath], {
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
