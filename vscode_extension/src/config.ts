import * as vscode from "vscode";
import { DEFAULT_DAFNY_COMMAND } from "@proofpulse/core";
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
    return custom || DEFAULT_DAFNY_COMMAND; // empty means "search PATH"
  }

  // Default: use bundled
  if (context && isBundledInstalled(context)) {
    return getBundledDafnyPath(context);
  }

  // Bundled not yet installed — fall back to PATH lookup (installer will handle it)
  return DEFAULT_DAFNY_COMMAND;
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

/** Solver binary the verifier runs with; empty = the verifier's own default. */
export function getSolverPath(): string {
  return vscode.workspace.getConfiguration("proofpulse").get<string>("solverPath", "").trim();
}

/** Z3 binary the core minimizer forwards to; empty = solverPath, else auto-resolve. */
export function getZ3Path(): string {
  return vscode.workspace.getConfiguration("proofpulse").get<string>("z3Path", "");
}

export function getDecorationOpacity(): number {
  const raw = vscode.workspace.getConfiguration("proofpulse").get<number>("decorationOpacity", 0.2);
  return Math.max(0.0, Math.min(0.5, raw));
}

export function getNoAbstractInterpretation(): boolean {
  return vscode.workspace.getConfiguration("proofpulse").get<boolean>("noAbstractInterpretation", false);
}

/** Also decorate implicit checks the verifier adds (null, index range, ...). */
export function getShowImplicitChecks(): boolean {
  return vscode.workspace.getConfiguration("proofpulse").get<boolean>("showImplicitChecks", false);
}
