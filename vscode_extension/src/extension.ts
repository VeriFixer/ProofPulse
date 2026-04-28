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

  // Run analysis when a .dfy file becomes the active editor (covers open, tab switch)
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      if (!editor) return;
      if (!editor.document.fileName.endsWith(".dfy")) return;
      if (!getRunOnSave()) return;
      runAnalysis(editor, context);
    }),
  );

  // Run on the already-active .dfy file at activation time
  const activeEditor = vscode.window.activeTextEditor;
  if (activeEditor && activeEditor.document.fileName.endsWith(".dfy") && getRunOnSave()) {
    runAnalysis(activeEditor, context);
  }
}

export function deactivate(): void {
  // Cleanup handled by disposables registered in context.subscriptions
}
