/**
 * Generate a YAML log of ProofPulse coverage analysis.
 *
 * Default (--log): only nodes that are Vacuous, Uncovered or CovTest.
 * Verbose (--log-verbose): same + complete proof dependency graph.
 */
import { CovStatus, TokenType, VacuityRole } from "./types.js";
import type { ProofNode } from "./proof-node.js";
import type { Proof } from "./proof.js";
import { flaggedExpressions, spanEndCol } from "./flagged-expressions.js";

export interface ReportOptions {
  verbose?: boolean;
  /** Also report implicit checks the verifier adds (null, range, ...). */
  includeImplicit?: boolean;
}

function typeLabel(type: TokenType): string {
  switch (type) {
    case TokenType.Postcondition: return "Postcondition";
    case TokenType.Precondition: return "Precondition";
    case TokenType.LoopInvariant: return "LoopInvariant";
    case TokenType.AssertionManual: return "AssertionManual";
    case TokenType.AssertionAutomatic: return "AssertionAutomatic";
    case TokenType.CodeLine: return "CodeLine";
    case TokenType.Call: return "Call";
    default: return "Unknown";
  }
}

/** Explanation for a Vacuous node, by its part in the contradiction. */
export function vacuityExplanation(role: VacuityRole | undefined): string {
  switch (role) {
    case VacuityRole.Goal: return "Proved vacuously: the facts on its path contradict each other, so it was never really checked.";
    case VacuityRole.Cause: return "Part of a contradiction that makes a proof vacuous.";
    case VacuityRole.Affected: return "Only reached under contradictory facts: unreachable in every proof that sees it.";
    default: return "Takes part only in vacuous proofs.";
  }
}

function statusExplanation(status: CovStatus, type: TokenType, role?: VacuityRole): string {
  if (status === CovStatus.Vacuous) return vacuityExplanation(role);
  if (status === CovStatus.Uncovered) {
    switch (type) {
      case TokenType.Postcondition: return "Postcondition not proven by any code path.";
      case TokenType.Precondition: return "Precondition not used in any proof obligation.";
      case TokenType.AssertionManual: return "Manual assertion not covered by proof dependencies.";
      case TokenType.LoopInvariant: return "Loop invariant not covered by proof dependencies.";
      case TokenType.CodeLine: return "Code line not contributing to any proof obligation.";
      default: return "Not covered by any proof path.";
    }
  }
  if (status === CovStatus.CovTest) {
    switch (type) {
      case TokenType.Postcondition: return "Postcondition not used in calling code — only in test assertions.";
      case TokenType.Precondition: return "Precondition only used in calling tests, unnecessary to prove postconditions.";
      case TokenType.CodeLine: return "Code used only by test assertions, not by postcondition proofs.";
      case TokenType.LoopInvariant: return "Loop invariant covered only by test paths, not postcondition proofs.";
      case TokenType.AssertionManual: return "Assertion covered only by test paths, not postcondition proofs.";
      default: return "Covered only by test/non-postcondition assertions.";
    }
  }
  return "Fully covered by postcondition proof dependencies.";
}

function yamlStr(s: string): string {
  if (/[:\n\r#"'{}[\],&*!|>%@`]/.test(s) || s.trim() !== s || s === "") {
    return JSON.stringify(s);
  }
  return s;
}

interface MethodBlock {
  name: string;
  startLine: number;
  endLine: number;
}

function extractMethods(sourceCode: string): MethodBlock[] {
  const lines = sourceCode.split("\n");
  const methods: MethodBlock[] = [];
  const declRe = /^\s*(method|function|predicate|lemma)\s+(\w+)/;

  for (let i = 0; i < lines.length; i++) {
    const m = lines[i].match(declRe);
    if (!m) continue;
    const name = `${m[1]} ${m[2]}`;
    const startLine = i + 1;
    let braceDepth = 0;
    let foundOpen = false;
    let endLine = lines.length;
    for (let j = i; j < lines.length; j++) {
      // Attributes such as {:trigger F(x)} are not blocks
      for (const ch of lines[j].replace(/\{:[^{}]*\}/g, "")) {
        if (ch === "{") { braceDepth++; foundOpen = true; }
        if (ch === "}") braceDepth--;
      }
      if (foundOpen && braceDepth <= 0) {
        endLine = j + 1;
        break;
      }
    }
    methods.push({ name, startLine, endLine });
  }

  return methods;
}

function getSourceLine(lines: string[], lineNum: number): string {
  return (lines[lineNum - 1] || "").trim();
}

/** Source text of a node's span (1-based columns, inclusive end), whitespace collapsed. */
function getSourceSpan(lines: string[], n: ProofNode): string {
  const parts: string[] = [];
  for (let l = n.start.line; l <= n.end.line; l++) {
    const text = lines[l - 1] ?? "";
    const from = l === n.start.line ? Math.max(0, n.start.col - 1) : 0;
    const to = l === n.end.line ? spanEndCol(text, n.end.col) : text.length;
    parts.push(text.slice(from, to));
  }
  const expr = parts.join(" ").replace(/\s+/g, " ").trim();
  if (expr.length === 0) return getSourceLine(lines, n.start.line);
  return expr.length > 100 ? expr.slice(0, 97) + "..." : expr;
}

/** `12-25` on one line, `12-3:8` when the span ends on a later line. */
function spanColumns(lines: string[], n: ProofNode): string {
  const end = spanEndCol(lines[n.end.line - 1] ?? "", n.end.col);
  return n.end.line === n.start.line ? `${n.start.col}-${end}` : `${n.start.col}-${n.end.line}:${end}`;
}

/**
 * Generate a YAML log from a Proof object.
 */
export function generateTextReport(
  sourceCode: string,
  proof: Proof,
  options?: ReportOptions,
): string {
  const verbose = options?.verbose ?? false;
  const graph = proof.proofGraph;
  const nodes = graph.getAllNodes();
  const lines = sourceCode.split("\n");
  const out: string[] = [];

  const methods = extractMethods(sourceCode);
  if (methods.length === 0) {
    methods.push({ name: "(file)", startLine: 1, endLine: lines.length });
  }

  const flagged = flaggedExpressions(nodes, { includeImplicit: options?.includeImplicit });
  for (const method of methods) {
    const methodNodes = flagged.filter(n => n.start.line >= method.startLine && n.start.line <= method.endLine);
    if (methodNodes.length === 0) continue;

    out.push("");
    out.push(`${method.name}:`);
    for (const n of methodNodes) {
      const status = n.getCovStatus();
      const lineText = getSourceLine(lines, n.start.line);
      const expr = getSourceSpan(lines, n);
      out.push(`  - line: ${n.start.line}`);
      out.push(`    cols: ${spanColumns(lines, n)}`);
      out.push(`    type: ${typeLabel(n.getType())}`);
      out.push(`    status: ${status}`);
      out.push(`    code: ${yamlStr(expr)}`);
      if (expr !== lineText) out.push(`    in: ${yamlStr(lineText)}`);
      out.push(`    message: ${yamlStr(statusExplanation(status, n.getType(), n.vacuity))}`);
    }
  }

  if (verbose) {
    const topNodes = graph.getAllTopNodes().filter(top => top.provedBy.size > 0);

    if (topNodes.length > 0) {
      out.push("");
      out.push("proof_dependencies:");
      for (const top of topNodes) {
        if (top.provedBy.size === 0) continue;
        const topCode = getSourceLine(lines, top.start.line);
        out.push(`  - assertion:`);
        out.push(`      type: ${typeLabel(top.getType())}`);
        out.push(`      line: ${top.start.line}`);
        out.push(`      status: ${top.getCovStatus()}`);
        out.push(`      code: ${yamlStr(topCode)}`);
        out.push(`      proof_text: ${yamlStr(top.prooftext)}`);
        out.push(`    proved_by:`);
        for (const dep of top.provedBy) {
          const depCode = getSourceLine(lines, dep.start.line);
          out.push(`      - type: ${typeLabel(dep.getType())}`);
          out.push(`        line: ${dep.start.line}`);
          out.push(`        status: ${dep.getCovStatus()}`);
          out.push(`        code: ${yamlStr(depCode)}`);
          out.push(`        proof_text: ${yamlStr(dep.prooftext)}`);
        }
      }
    }
  }

  if (out.length === 0) {
    out.push("");
    out.push("# All nodes fully covered — nothing to report.");
  }

  return out.join("\n");
}
