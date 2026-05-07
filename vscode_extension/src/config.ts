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

export function getForceMinimization(): boolean {
  return vscode.workspace.getConfiguration("proofpulse").get<boolean>("forceMinimization", true);
}

export function getZ3Path(): string {
  return vscode.workspace.getConfiguration("proofpulse").get<string>("z3Path", "");
}

export function getDecorationOpacity(): number {
  const raw = vscode.workspace.getConfiguration("proofpulse").get<number>("decorationOpacity", 0.08);
  return Math.max(0.0, Math.min(0.5, raw));
}
