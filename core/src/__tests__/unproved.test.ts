import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { analyzeReport, parseProof } from "../proof.js";
import { ProofGraph } from "../proof-graph.js";
import { inUnprovedUnit, unprovedGoals } from "../coverage.js";
import { flaggedExpressions } from "../flagged-expressions.js";
import { CoverageReport, NodeKind, QueryOutcome, ReportQuery, UnitKind } from "../report/coverage-report.js";
import { CovStatus } from "../types.js";

// Real Dafny log (proofpulse-ci image, --isolate-assertions, coverage report on):
// the postcondition on the early `return true` path fails only under dependency tracking.
const SOURCE = readFileSync(resolve(__dirname, "fixtures", "unproved-under-tracking.dfy"), "utf8");
const LOG = readFileSync(resolve(__dirname, "fixtures", "unproved-under-tracking.log"), "utf8");

describe("Unproved goals from a real Dafny log", () => {
  const proof = parseProof(SOURCE, LOG);

  it("marks the failed postcondition Unproved, although another return path proves it", () => {
    expect(proof.lineStatus[1]).toBe(CovStatus.Unproved);
    const goals = unprovedGoals(proof.proofGraph);
    expect(goals.map(g => [g.start.line, g.failedOutcome])).toEqual([[2, QueryOutcome.Invalid]]);
  });

  it("keeps the other statuses, but flags the unused facts of that method as possibly wrong", () => {
    // Invariant 1 and `return true`: only the failed goal needs them
    expect(proof.lineStatus[5]).toBe(CovStatus.Uncovered);
    expect(proof.lineStatus[10]).toBe(CovStatus.Uncovered);
    expect(proof.lineStatus[6]).toBe(CovStatus.CovComplete);
    const nodes = proof.proofGraph.getAllNodes();
    const mayBeWrong = inUnprovedUnit(nodes);
    const flaggedLines = new Set(nodes.filter(mayBeWrong).map(n => n.start.line));
    expect(flaggedLines.has(6)).toBe(true);
    expect(flaggedLines.has(11)).toBe(true);
    // Covered facts and the postcondition get no note
    expect(flaggedLines.has(7)).toBe(false);
    expect(flaggedLines.has(2)).toBe(false);
  });
});

describe("Unproved goals in the language-neutral core", () => {
  const span = (line: number) => ({ file: "f0", start: { line, col: 1 }, end: { line, col: 5 } });
  const query = (id: string, outcome: QueryOutcome, goals: string[], used: string[], unused: string[]): ReportQuery =>
    ({ id, index: 0, outcome, goals, used, unused });

  /** Unit a: n1 proved from n0 (n2 unused), n3 failed. Unit b: n5 proved from n4 (n6 unused). */
  function report(failedOutcome: QueryOutcome | null): CoverageReport {
    return {
      schema: "proofpulse-coverage/v1",
      tool: { name: "kani" as never },
      sources: [{ id: "f0", path: "lib.rs" }],
      units: [
        {
          id: "u0", name: "a", kind: UnitKind.Harness,
          queries: [
            query("q0", QueryOutcome.Valid, ["n1"], ["n0"], ["n2"]),
            ...(failedOutcome ? [query("q1", failedOutcome, ["n3"], [], [])] : []),
          ],
        },
        { id: "u1", name: "b", kind: UnitKind.Harness, queries: [query("q2", QueryOutcome.Valid, ["n5"], ["n4"], ["n6"])] },
      ],
      nodes: [
        { id: "n0", kind: NodeKind.Assume, span: span(1), message: "assume" },
        { id: "n1", kind: NodeKind.Postcondition, span: span(2), message: "property" },
        { id: "n2", kind: NodeKind.Code, span: span(3), message: "statement" },
        { id: "n3", kind: NodeKind.ImplicitCheck, span: span(4), message: "index in range" },
        { id: "n4", kind: NodeKind.Assume, span: span(5), message: "assume" },
        { id: "n5", kind: NodeKind.Postcondition, span: span(6), message: "property" },
        { id: "n6", kind: NodeKind.Code, span: span(7), message: "statement" },
      ],
    };
  }
  const SRC = "1\n2\n3\n4\n5\n6\n7\n";

  it("marks only the failed goal, and notes possibly wrong statuses in its unit only", () => {
    const proof = analyzeReport(SRC, report(QueryOutcome.TimeOut));
    expect(proof.lineStatus.slice(0, 7)).toEqual([
      CovStatus.CovComplete, CovStatus.CovTest, CovStatus.Uncovered, CovStatus.Unproved,
      CovStatus.CovComplete, CovStatus.CovTest, CovStatus.Uncovered,
    ]);
    const nodes = proof.proofGraph.getAllNodes();
    expect(nodes.filter(inUnprovedUnit(nodes)).map(n => n.start.line)).toEqual([3]);
  });

  it("shows an unproved implicit check, which is otherwise hidden", () => {
    const proof = analyzeReport(SRC, report(QueryOutcome.Invalid));
    const flagged = flaggedExpressions(proof.proofGraph.getAllNodes());
    expect(flagged.map(n => [n.start.line, n.getCovStatus()])).toContainEqual([4, CovStatus.Unproved]);
  });

  it("keeps the outcome through YAML, and writes it only when a query failed", () => {
    const failed = analyzeReport(SRC, report(QueryOutcome.OutOfResource)).proofGraph;
    const restored = new ProofGraph();
    restored.fromYAML(failed.toYAML());
    expect(unprovedGoals(restored).map(n => n.failedOutcome)).toEqual([QueryOutcome.OutOfResource]);
    expect(analyzeReport(SRC, report(null)).proofGraph.toYAML()).not.toContain("failedOutcome");
  });
});
