/**
 * Generate a YAML log of ProofPulse coverage analysis.
 *
 * Default (--log): only nodes that are Uncovered or CovTest. Nothing else.
 * Verbose (--log-verbose): same as default + complete proof dependency graph.
 *
 * Reports per method/function — only methods with flagged nodes are shown.
 */
import { CovStatus, TokenType } from "./types.js";
import type { Node } from "./node.js";
import type { Proof } from "./proof.js";

export interface ReportOptions {
  /** If true, also include the complete proof dependency graph after the flagged nodes. */
  verbose?: boolean;
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

/** Same wording as the web UI (web_viewer/app.js statusExplanation). */
function statusExplanation(status: CovStatus, type: TokenType): string {
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
      for (const ch of lines[j]) {
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

/** Get the source code line for a given line number (1-based). */
function getSourceLine(lines: string[], lineNum: number): string {
  return (lines[lineNum - 1] || "").trim();
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
  // Per-method flagged nodes
  for (const method of methods) {
    const methodNodes = nodes.filter(n => n.start.line >= method.startLine && n.start.line <= method.endLine);
    const flagged = methodNodes.filter(n => n.covStatus === CovStatus.Uncovered || n.covStatus === CovStatus.CovTest);
    if (flagged.length === 0) continue;

    // Deduplicate by line — keep the worst status
    const byLine = new Map<number, Node[]>();
    for (const n of flagged) {
      const l = n.start.line;
      if (!byLine.has(l)) byLine.set(l, []);
      byLine.get(l)!.push(n);
    }

    out.push("");
    out.push(`${method.name}:`);
    for (const [line, lineNodes] of [...byLine.entries()].sort((a, b) => a[0] - b[0])) {
      const worst = lineNodes.some(n => n.covStatus === CovStatus.Uncovered) ? CovStatus.Uncovered
        : CovStatus.CovTest;
      const representative = lineNodes[0];
      const codeLine = getSourceLine(lines, line);
      out.push(`  - line: ${line}`);
      out.push(`    type: ${typeLabel(representative.type)}`);
      out.push(`    status: ${worst}`);
      out.push(`    code: ${yamlStr(codeLine)}`);
      out.push(`    message: ${yamlStr(statusExplanation(worst, representative.type))}`);
    }
  }

  // Verbose: complete proof dependency graph
  if (verbose) {
    const topNodes = graph.getAllTopNodes().filter(top => {
      const deps = graph.getBFSNeighbors(top.id, true, false);
      return deps && deps.length > 0;
    });

    if (topNodes.length > 0) {
      out.push("");
      out.push("proof_dependencies:");
      for (const top of topNodes) {
        const deps = graph.getBFSNeighbors(top.id, true, false);
        if (!deps || deps.length === 0) continue;
        const topCode = getSourceLine(lines, top.start.line);
        out.push(`  - assertion:`);
        out.push(`      type: ${typeLabel(top.type)}`);
        out.push(`      line: ${top.start.line}`);
        out.push(`      status: ${top.covStatus}`);
        out.push(`      code: ${yamlStr(topCode)}`);
        out.push(`      proof_text: ${yamlStr(top.prooftext)}`);
        out.push(`    proved_by:`);
        for (const dep of deps) {
          const depCode = getSourceLine(lines, dep.node.start.line);
          out.push(`      - type: ${typeLabel(dep.node.type)}`);
          out.push(`        line: ${dep.node.start.line}`);
          out.push(`        status: ${dep.node.covStatus}`);
          out.push(`        code: ${yamlStr(depCode)}`);
          out.push(`        proof_text: ${yamlStr(dep.node.prooftext)}`);
        }
      }
    }
  }

  if (out.length === 1) {
    out.push("");
    out.push("# All nodes fully covered — nothing to report.");
  }

  return out.join("\n");
}
