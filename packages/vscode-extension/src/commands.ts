import * as vscode from "vscode";
import { runDafny, parseProof } from "@proofpulse/core";
import { getDafnyPath, getTimeout } from "./config";
import { applyDecorations } from "./decorations";
import { ProofPulseHoverProvider } from "./hover";

let hoverDisposable: vscode.Disposable | undefined;

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
        });

        if (result.error) {
          vscode.window.showErrorMessage(`ProofPulse: ${result.error}`);
          return;
        }

        const proof = parseProof(sourceCode, result.log);
        applyDecorations(editor, proof.lineStatus, proof.proofGraph.getAllNodes());

        if (hoverDisposable) {
          hoverDisposable.dispose();
        }
        hoverDisposable = vscode.languages.registerHoverProvider(
          { scheme: "file", language: "dafny" },
          new ProofPulseHoverProvider(proof.proofGraph),
        );
        context.subscriptions.push(hoverDisposable);
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
