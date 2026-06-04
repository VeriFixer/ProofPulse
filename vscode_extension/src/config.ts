import * as vscode from "vscode";
import { isBundledInstalled, getBundledDafnyPath } from "./dafny-installer";

/**
 * Resolve dafny path. Priority:
 * 1. If useCustomDafny=true → use customDafnyPath (or "dafny" if empty)
 * 2. Otherwise → bundled ProofPulse install
 */
export function getDafnyPath(context?: vscode.ExtensionContext): string {
  const cfg = vscode.workspace.getConfiguration("proofpulse");
  const useCustom = cfg.get<boolean>("useCustomDafny", false);

  if (useCustom) {
    const custom = cfg.get<string>("customDafnyPath", "")?.trim();
    return custom || "dafny"; // empty means "search PATH"
  }

  // Default: use bundled
  if (context && isBundledInstalled(context)) {
    return getBundledDafnyPath(context);
  }

  // Bundled not yet installed — return "dafny" as fallback (installer will handle it)
  return "dafny";
}

export function getTimeout(): number {
  return vscode.workspace.getConfiguration("proofpulse").get<number>("timeoutSeconds", 60);
}

export function getRunOnSave(): boolean {
  return vscode.workspace.getConfiguration("proofpulse").get<boolean>("runOnSave", true);
}

export function getForceMinimization(): boolean {
  return vscode.workspace.getConfiguration("proofpulse").get<boolean>("forceMinimization", false);
}

export function getZ3Path(): string {
  return vscode.workspace.getConfiguration("proofpulse").get<string>("z3Path", "");
}

export function getDecorationOpacity(): number {
  const raw = vscode.workspace.getConfiguration("proofpulse").get<number>("decorationOpacity", 0.08);
  return Math.max(0.0, Math.min(0.5, raw));
}

export function getNoAbstractInterpretation(): boolean {
  return vscode.workspace.getConfiguration("proofpulse").get<boolean>("noAbstractInterpretation", false);
}
