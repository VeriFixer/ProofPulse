import { describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { dafnyLogToReport } from "../backends/dafny/log-parser.js";
import { analyzeReport, parseProof } from "../proof.js";
import { ProofGraph } from "../proof-graph.js";
import { ProofNode } from "../proof-node.js";
import { computeLineStatus } from "../coverage.js";
import { validateCoverageReport, ReportValidationError } from "../report/validate.js";
import { CoverageReport, NodeKind, UnitKind, Vacuity } from "../report/coverage-report.js";
import { CovStatus, VacuityRole } from "../types.js";

// Real Dafny log (proofpulse-ci image, --isolate-assertions, coverage report on) for fixtures/vacuity.dfy.
const SOURCE = readFileSync(resolve(__dirname, "fixtures", "vacuity.dfy"), "utf8");
const LOG = readFileSync(resolve(__dirname, "fixtures", "vacuity.log"), "utf8");

/** Vacuity of every query of a unit, in order. */
function unitVacuity(report: CoverageReport, name: string): Array<Vacuity | undefined> {
  const unit = report.units.find((u) => u.name === name);
  if (!unit) throw new Error(`no unit ${name}`);
  return unit.queries.map((q) => q.vacuity);
}

function nodeAt(graph: ProofGraph, line: number, col: number): ProofNode {
  const node = graph.getAllNodes().find((n) => n.start.line === line && n.start.col === col);
  if (!node) throw new Error(`no node at ${line}:${col}`);
  return node;
}

describe("Dafny adapter: query vacuity", () => {
  const report = dafnyLogToReport(LOG, { sourceText: SOURCE });

  it("flags queries whose goal is reported unused", () => {
    expect(unitVacuity(report, "IncVacuous")).toEqual([Vacuity.Vacuous]);
    expect(unitVacuity(report, "AssumeFalse")).toEqual([Vacuity.Vacuous]);
  });

  it("leaves ordinary proofs alone", () => {
    expect(unitVacuity(report, "IncOk")).toEqual([undefined]);
  });

  it("flags only the dead-branch assertion, not the method's postcondition", () => {
    expect(unitVacuity(report, "DeadBranch")).toEqual([undefined, Vacuity.Vacuous]);
  });

  it("marks `assert false` and `{:contradiction}` goals as intentional", () => {
    // One query per postcondition conjunct, then the `assert false`.
    expect(unitVacuity(report, "MaxIsUpperBound")).toEqual([undefined, undefined, Vacuity.Intentional]);
    expect(unitVacuity(report, "AbsNonNegative")).toContain(Vacuity.Intentional);
    expect(unitVacuity(report, "AbsNonNegative")).not.toContain(Vacuity.Vacuous);
  });

  it("without the source text, intentional contradictions count as vacuous", () => {
    const noSource = dafnyLogToReport(LOG);
    expect(unitVacuity(noSource, "MaxIsUpperBound")).toEqual([undefined, undefined, Vacuity.Vacuous]);
  });

  it("produces a report that passes validation", () => {
    expect(() => validateCoverageReport(JSON.parse(JSON.stringify(report)))).not.toThrow();
  });
});

describe("Vacuity roles and coverage status", () => {
  const proof = parseProof(SOURCE, LOG);
  const graph = proof.proofGraph;

  it("contradictory preconditions: goal, causes and affected code are Vacuous", () => {
    expect(nodeAt(graph, 5, 11).vacuity).toBe(VacuityRole.Goal);
    expect(nodeAt(graph, 3, 12).vacuity).toBe(VacuityRole.Cause);
    expect(nodeAt(graph, 4, 12).vacuity).toBe(VacuityRole.Cause);
    expect(nodeAt(graph, 7, 3).vacuity).toBe(VacuityRole.Affected);
    for (const [line, col] of [[3, 12], [4, 12], [5, 11], [7, 3]]) {
      expect(nodeAt(graph, line, col).getCovStatus()).toBe(CovStatus.Vacuous);
    }
  });

  it("a precondition that also proves a real goal is not a cause", () => {
    // DeadBranch: `requires x > 0` proves the postcondition and also makes the branch dead.
    const pre = nodeAt(graph, 28, 12);
    expect(pre.vacuity).toBeUndefined();
    expect(pre.getCovStatus()).not.toBe(CovStatus.Vacuous);
    expect(nodeAt(graph, 32, 5).getCovStatus()).toBe(CovStatus.Vacuous);
  });

  it("proofs by contradiction keep their normal status", () => {
    expect(nodeAt(graph, 45, 5).vacuity).toBe(VacuityRole.Intentional);
    expect(nodeAt(graph, 45, 5).getCovStatus()).toBe(CovStatus.CovComplete);
    expect(nodeAt(graph, 55, 5).vacuity).toBe(VacuityRole.Intentional);
    expect(nodeAt(graph, 41, 12).getCovStatus()).toBe(CovStatus.CovComplete);
  });

  it("ordinary methods get no vacuity role", () => {
    for (const n of graph.getAllNodes().filter((n) => n.methodName === "IncOk")) {
      expect(n.vacuity).toBeUndefined();
    }
  });

  it("line status shows Vacuous on the affected lines only", () => {
    const vacuousLines = proof.lineStatus.flatMap((s, i) => (s === CovStatus.Vacuous ? [i + 1] : []));
    expect(vacuousLines).toEqual([3, 4, 5, 7, 8, 20, 22, 23, 24, 32]);
  });

  it("graph YAML keeps vacuity roles", () => {
    const reloaded = new ProofGraph();
    reloaded.fromYAML(graph.toYAML());
    expect(nodeAt(reloaded, 3, 12).vacuity).toBe(VacuityRole.Cause);
    expect(nodeAt(reloaded, 45, 5).vacuity).toBe(VacuityRole.Intentional);
  });
});

describe("Vacuity in the language-neutral core", () => {
  /** Minimal report: one unit, one query over a precondition, a postcondition and a code line. */
  function report(vacuity?: Vacuity): CoverageReport {
    const span = (line: number) => ({ file: "f0", start: { line, col: 1 }, end: { line, col: 5 } });
    return {
      schema: "proofpulse-coverage/v1",
      tool: { name: "kani" as never },
      sources: [{ id: "f0", path: "lib.rs" }],
      units: [{
        id: "u0", name: "harness", kind: UnitKind.Harness,
        queries: [{ id: "q0", index: 0, outcome: "Valid" as never, goals: ["n1"], used: ["n0"], unused: ["n2"], ...(vacuity ? { vacuity } : {}) }],
      }],
      nodes: [
        { id: "n0", kind: NodeKind.Assume, span: span(1), message: "assume" },
        { id: "n1", kind: NodeKind.Postcondition, span: span(2), message: "property" },
        { id: "n2", kind: NodeKind.Code, span: span(3), message: "statement" },
      ],
    };
  }

  it("any backend can mark a query vacuous", () => {
    const proof = analyzeReport("a\nb\nc\n", report(Vacuity.Vacuous));
    expect(proof.lineStatus.slice(0, 3)).toEqual([CovStatus.Vacuous, CovStatus.Vacuous, CovStatus.Vacuous]);
  });

  it("an unmarked query is unaffected", () => {
    const proof = analyzeReport("a\nb\nc\n", report());
    expect(proof.lineStatus).not.toContain(CovStatus.Vacuous);
    expect(proof.proofGraph.toYAML()).not.toContain("vacuity");
  });

  it("validation rejects an unknown vacuity value", () => {
    const bad = JSON.parse(JSON.stringify(report())) as Record<string, any>;
    bad.units[0].queries[0].vacuity = "maybe";
    expect(() => validateCoverageReport(bad)).toThrow(ReportValidationError);
  });

  it("Vacuous wins over a covered node on the same span", () => {
    const graph = new ProofGraph();
    for (const [method, status] of [["a", CovStatus.CovComplete], ["b", CovStatus.Vacuous]] as const) {
      const n = new ProofNode("lib.rs", { line: 1, col: 1 }, { line: 1, col: 5 }, method, UnitKind.Harness, "x", NodeKind.Code);
      n.setCovStatus(status);
      graph.addNode(n);
    }
    expect(computeLineStatus(graph, "x\n")[0]).toBe(CovStatus.Vacuous);
  });
});
