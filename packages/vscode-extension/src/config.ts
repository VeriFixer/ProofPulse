import * as vscode from "vscode";

export function getDafnyPath(): string {
  return vscode.workspace.getConfiguration("proofpulse").get<string>("dafnyPath", "dafny");
}

export function getTimeout(): number {
  return vscode.workspace.getConfiguration("proofpulse").get<number>("timeoutSeconds", 60);
}

export function getRunOnSave(): boolean {
  return vscode.workspace.getConfiguration("proofpulse").get<boolean>("runOnSave", true);
}
