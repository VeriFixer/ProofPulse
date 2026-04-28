import * as vscode from "vscode";
import { registerRunAnalysis, registerGetProofReport, runAnalysis } from "./commands";
import { clearDecorations } from "./decorations";
import { getRunOnSave } from "./config";

export function activate(context: vscode.ExtensionContext): void {
  registerRunAnalysis(context);
  registerGetProofReport(context);

  // Clear decorations on edit (stale until next analysis)
  context.subscriptions.push(
    vscode.workspace.onDidChangeTextDocument((e) => {
      if (!e.document.fileName.endsWith(".dfy")) return;
      const editor = vscode.window.activeTextEditor;
      if (editor && editor.document === e.document) {
        clearDecorations(editor);
      }
    }),
  );

  // Run analysis on save for .dfy files
  context.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument((doc) => {
      if (!doc.fileName.endsWith(".dfy")) return;
      if (!getRunOnSave()) return;
      const editor = vscode.window.visibleTextEditors.find((e) => e.document === doc);
      if (editor) {
        runAnalysis(editor, context);
      }
    }),
  );
}

export function deactivate(): void {
  // Cleanup handled by disposables registered in context.subscriptions
}
