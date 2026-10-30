import { describe, it, expect } from "vitest";
import { flaggedExpressions, spanEndCol } from "../flagged-expressions.js";
import { ProofNode } from "../proof-node.js";
import { ProofGraph } from "../proof-graph.js";
import { generateSpansFragment } from "../rendering.js";
import { NodeKind, UnitKind } from "../report/coverage-report.js";
import { CovStatus } from "../types.js";

function node(startCol: number, endCol: number, status: CovStatus, kind = NodeKind.Invariant): ProofNode {
  const n = new ProofNode("f.dfy", { line: 1, col: startCol }, { line: 1, col: endCol }, "M", UnitKind.Correctness, "x", kind);
  n.setCovStatus(status);
  return n;
}

const cols = (ns: ProofNode[]) => ns.map(n => [n.start.col, n.end.col]);

describe("flaggedExpressions", () => {
  it("reports only the uncovered part of a partly covered clause", () => {
    // invariant 0 <= i <= n: clause, `0 <= i` uncovered, `i <= n` covered
    const clause = node(11, 22, CovStatus.Uncovered);
    const lower = node(11, 16, CovStatus.Uncovered);
    const upper = node(16, 22, CovStatus.CovComplete);
    expect(cols(flaggedExpressions([clause, lower, upper]))).toEqual([[11, 16]]);
  });

  it("reports a fully uncovered clause once, as a whole", () => {
    const clause = node(11, 22, CovStatus.Uncovered);
    const lower = node(11, 16, CovStatus.Uncovered);
    const upper = node(16, 22, CovStatus.Uncovered);
    expect(cols(flaggedExpressions([upper, lower, clause]))).toEqual([[11, 22]]);
  });

  it("reports the innermost parts when their statuses differ", () => {
    const clause = node(11, 22, CovStatus.Uncovered);
    const lower = node(11, 16, CovStatus.Uncovered);
    const upper = node(16, 22, CovStatus.CovTest);
    expect(cols(flaggedExpressions([clause, lower, upper]))).toEqual([[11, 16], [16, 22]]);
  });

  it("hides implicit checks unless asked, but always shows vacuous ones", () => {
    const check = node(3, 8, CovStatus.Uncovered, NodeKind.ImplicitCheck);
    const vacuousCheck = node(10, 14, CovStatus.Vacuous, NodeKind.ImplicitCheck);
    expect(cols(flaggedExpressions([check, vacuousCheck]))).toEqual([[10, 14]]);
    expect(cols(flaggedExpressions([check, vacuousCheck], { includeImplicit: true }))).toEqual([[3, 8], [10, 14]]);
  });

  it("never reports a clause whose parts are covered", () => {
    // the report has an unused node for the whole clause, but its parts are used
    const clause = node(11, 22, CovStatus.Uncovered);
    const lower = node(11, 16, CovStatus.CovComplete);
    const upper = node(16, 22, CovStatus.CovComplete);
    expect(flaggedExpressions([clause, lower, upper])).toEqual([]);
  });

  it("judges a clause by its clause parts, not by checks or calls inside it", () => {
    const clause = node(11, 30, CovStatus.Uncovered);
    const call = node(20, 30, CovStatus.CovComplete, NodeKind.Code);
    expect(cols(flaggedExpressions([clause, call]))).toEqual([[11, 30]]);
  });

  it("drops covered expressions", () => {
    expect(flaggedExpressions([node(1, 5, CovStatus.CovComplete)])).toEqual([]);
  });
});

describe("spanEndCol", () => {
  const line = "    requires 0 <= n < arr.Length && x >= 0.0;";
  it("extends an end column at a token start over the whole token", () => {
    expect(line.slice(18, spanEndCol(line, line.indexOf("Length") + 1))).toBe("n < arr.Length");
    expect(line.slice(36, spanEndCol(line, line.indexOf("0.0") + 1))).toBe("x >= 0.0");
  });
  it("covers string and char literals up to the closing quote", () => {
    const lit = `    requires forall i :: s[i] == '(' || s[i] == ')' && t in "ab\\"c"`;
    expect(lit.slice(0, spanEndCol(lit, lit.indexOf("')'") + 1))).toMatch(/== '\)'$/);
    expect(lit.slice(0, spanEndCol(lit, lit.indexOf('"ab') + 1))).toMatch(/"ab\\"c"$/);
    const prime = "    ensures x' == y";
    expect(spanEndCol(prime, prime.indexOf("'") + 1)).toBe(prime.indexOf("'") + 1);
  });
  it("leaves one-character tokens alone", () => {
    expect(spanEndCol(line, line.indexOf(";") + 1)).toBe(line.indexOf(";") + 1);
  });
});

describe("generateSpansFragment", () => {
  it("covers the whole last token of a span", () => {
    const code = "    requires 0 <= n < arr.Length";
    const graph = new ProofGraph();
    const n = new ProofNode("f.dfy", { line: 1, col: 19 }, { line: 1, col: 27 }, "M", UnitKind.Correctness, "x", NodeKind.Precondition);
    n.setCovStatus(CovStatus.Uncovered);
    graph.addNode(n);
    expect(generateSpansFragment(code, graph)).toMatch(/>n &lt; arr\.Length<\/span>/);
  });
});
