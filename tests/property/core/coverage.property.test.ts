import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { computeLineStatus } from "../../../core/src/coverage.js";
import { CovStatus } from "../../../core/src/types.js";
import { ProofNode } from "../../../core/src/proof-node.js";
import { ProofGraph } from "../../../core/src/proof-graph.js";

/**
 * Property 6: Line status uses two-level aggregation
 * Validates: Requirements 4.1
 *
 * 1. Group nodes by exact span (start,col-end,col)
 * 2. Within same span: best-case (CovComplete > CovTest > Uncovered)
 * 3. Across distinct spans on same line: worst-case (Uncovered > CovTest > CovComplete)
 * 4. Default CovComplete for lines with no tokens.
 */

const FILE = "test.dfy";
const COV_STATUSES = [CovStatus.CovComplete, CovStatus.CovTest, CovStatus.Uncovered] as const;

function bestCase(a: CovStatus, b: CovStatus): CovStatus {
  const rank: Record<CovStatus, number> = {
    [CovStatus.CovComplete]: 2,
    [CovStatus.CovTest]: 1,
    [CovStatus.Uncovered]: 0,
  };
  return rank[a] >= rank[b] ? a : b;
}

function worstCase(a: CovStatus, b: CovStatus): CovStatus {
  const rank: Record<CovStatus, number> = {
    [CovStatus.CovComplete]: 2,
    [CovStatus.CovTest]: 1,
    [CovStatus.Uncovered]: 0,
  };
  return rank[a] <= rank[b] ? a : b;
}

/** Node spec with explicit span columns for testing two-level logic. */
interface NodeSpec {
  startLine: number;
  startCol: number;
  endCol: number;
  covStatus: CovStatus;
}

/**
 * Generator: nodes with explicit spans. Some share spans (same col range),
 * some have distinct spans on the same line.
 */
const arbScenario = fc
  .integer({ min: 1, max: 20 })
  .chain((lineCount) =>
    fc
      .array(
        fc.record({
          startLine: fc.integer({ min: 1, max: lineCount }),
          startCol: fc.integer({ min: 1, max: 10 }),
          endCol: fc.integer({ min: 11, max: 20 }),
          covStatus: fc.constantFrom(...COV_STATUSES),
        }),
        { minLength: 0, maxLength: 15 },
      )
      .map((nodes) => ({ lineCount, nodes })),
  );

/** Build a ProofGraph from node specs with explicit columns. */
function buildGraph(specs: NodeSpec[]): ProofGraph {
  const graph = new ProofGraph();
  specs.forEach((spec, i) => {
    const node = new ProofNode(
      FILE,
      { line: spec.startLine, col: spec.startCol },
      { line: spec.startLine, col: spec.endCol },
      `method_${i}`,
      "",
      `token ${i}`,
    );
    node.setCovStatus(spec.covStatus);
    graph.addNode(node);
  });
  return graph;
}

/** Compute expected using two-level logic independently. */
function computeExpected(lineCount: number, specs: NodeSpec[]): CovStatus[] {
  const result = new Array<CovStatus>(lineCount).fill(CovStatus.CovComplete);

  // Group by line → span → statuses
  const lineSpans = new Map<number, Map<string, CovStatus>>();
  for (const spec of specs) {
    const idx = Math.max(0, spec.startLine - 1);
    if (idx >= lineCount) continue;
    const spanKey = `${spec.startLine},${spec.startCol}-${spec.startLine},${spec.endCol}`;
    if (!lineSpans.has(idx)) lineSpans.set(idx, new Map());
    const spans = lineSpans.get(idx)!;
    const existing = spans.get(spanKey);
    if (existing === undefined) {
      spans.set(spanKey, spec.covStatus);
    } else {
      spans.set(spanKey, bestCase(existing, spec.covStatus));
    }
  }

  for (const [idx, spans] of lineSpans) {
    let lineStatus: CovStatus = CovStatus.CovComplete;
    for (const spanStatus of spans.values()) {
      lineStatus = worstCase(lineStatus, spanStatus);
    }
    result[idx] = lineStatus;
  }

  return result;
}

describe("Property 6: Line status uses two-level span aggregation", () => {
  it("computeLineStatus matches independent two-level computation for all generated scenarios", () => {
    fc.assert(
      fc.property(arbScenario, ({ lineCount, nodes }) => {
        const sourceCode = Array.from(
          { length: lineCount },
          (_, i) => `line ${i + 1}`,
        ).join("\n");

        const graph = buildGraph(nodes);
        const actual = computeLineStatus(graph, sourceCode);
        const expected = computeExpected(lineCount, nodes);

        expect(actual).toEqual(expected);
      }),
      { numRuns: 200 },
    );
  });

  it("lines with no nodes default to CovComplete", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 30 }),
        (lineCount) => {
          const sourceCode = Array.from(
            { length: lineCount },
            (_, i) => `line ${i + 1}`,
          ).join("\n");

          const graph = new ProofGraph();
          const actual = computeLineStatus(graph, sourceCode);

          for (const status of actual) {
            expect(status).toBe(CovStatus.CovComplete);
          }
        },
      ),
      { numRuns: 100 },
    );
  });

  it("same span with mixed statuses picks best-case; distinct uncovered span makes line uncovered", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 10 }).chain((lineCount) =>
          fc
            .integer({ min: 1, max: lineCount })
            .chain((targetLine) =>
              fc
                .array(fc.constantFrom(...COV_STATUSES), {
                  minLength: 1,
                  maxLength: 5,
                })
                .map((sameSpanStatuses) => ({
                  lineCount,
                  targetLine,
                  sameSpanStatuses,
                })),
            ),
        ),
        ({ lineCount, targetLine, sameSpanStatuses }) => {
          // All nodes share the same span (col 3-8)
          const specs: NodeSpec[] = sameSpanStatuses.map((s) => ({
            startLine: targetLine,
            startCol: 3,
            endCol: 8,
            covStatus: s,
          }));

          const sourceCode = Array.from(
            { length: lineCount },
            (_, i) => `line ${i + 1}`,
          ).join("\n");

          const graph = buildGraph(specs);
          const actual = computeLineStatus(graph, sourceCode);

          // Same span → best-case
          let expected: CovStatus = CovStatus.Uncovered;
          for (const s of sameSpanStatuses) {
            expected = bestCase(expected, s);
          }
          expect(actual[targetLine - 1]).toBe(expected);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("distinct uncovered span on a line overrides other covered spans", () => {
    // Two distinct spans: one CovComplete, one Uncovered → line is Uncovered
    const sourceCode = "line 1\nline 2";
    const graph = new ProofGraph();

    const n1 = new ProofNode(FILE, { line: 1, col: 1 }, { line: 1, col: 5 }, "m1", "", "t1");
    n1.setCovStatus(CovStatus.CovComplete);
    graph.addNode(n1);

    const n2 = new ProofNode(FILE, { line: 1, col: 6 }, { line: 1, col: 10 }, "m2", "", "t2");
    n2.setCovStatus(CovStatus.Uncovered);
    graph.addNode(n2);

    const actual = computeLineStatus(graph, sourceCode);
    expect(actual[0]).toBe(CovStatus.Uncovered);
  });
});


/**
 * Property 8: getNodesByLine returns exactly span-containing nodes
 * Validates: Requirements 4.4
 *
 * For any ProofGraph and any line number, getNodesByLine SHALL return exactly
 * the nodes where start.line <= line <= end.line.
 */

import { getNodesByLine } from "../../../core/src/coverage.js";

/** Node with a random span: start line <= end line, random columns */
interface SpanNodeSpec {
  startLine: number;
  endLine: number;
  startCol: number;
  endCol: number;
}

/**
 * Generator: random nodes with random spans within a line range,
 * plus a random query line to test against.
 */
const arbSpanScenario = fc
  .integer({ min: 1, max: 30 })
  .chain((maxLine) =>
    fc
      .tuple(
        fc.array(
          fc.record({
            startLine: fc.integer({ min: 1, max: maxLine }),
            endLine: fc.integer({ min: 1, max: maxLine }),
            startCol: fc.integer({ min: 1, max: 80 }),
            endCol: fc.integer({ min: 1, max: 80 }),
          }).map((r): SpanNodeSpec => ({
            startLine: Math.min(r.startLine, r.endLine),
            endLine: Math.max(r.startLine, r.endLine),
            startCol: r.startCol,
            endCol: r.endCol,
          })),
          { minLength: 0, maxLength: 20 },
        ),
        fc.integer({ min: 1, max: maxLine }),
      )
      .map(([nodes, queryLine]) => ({ maxLine, nodes, queryLine })),
  );

function buildSpanGraph(specs: SpanNodeSpec[]): ProofGraph {
  const graph = new ProofGraph();
  specs.forEach((spec, i) => {
    const node = new ProofNode(
      FILE,
      { line: spec.startLine, col: spec.startCol },
      { line: spec.endLine, col: spec.endCol },
      "",
      "",
      `span token ${i}`,
    );
    graph.addNode(node);
  });
  return graph;
}

describe("Property 8: getNodesByLine returns exactly span-containing nodes", () => {
  it("returns exactly nodes where start.line <= queryLine <= end.line", () => {
    fc.assert(
      fc.property(arbSpanScenario, ({ nodes, queryLine }) => {
        const graph = buildSpanGraph(nodes);
        const allNodes = graph.getAllNodes();
        const result = getNodesByLine(graph, queryLine);

        // Expected: filter all nodes whose span contains queryLine
        const expected = allNodes.filter(
          (n) => n.start.line <= queryLine && queryLine <= n.end.line,
        );

        // Compare by sorted IDs for order-independence
        const resultIds = result.map((n) => n.getId()).sort();
        const expectedIds = expected.map((n) => n.getId()).sort();

        expect(resultIds).toEqual(expectedIds);
      }),
      { numRuns: 200 },
    );
  });

  it("returns empty array when queryLine is outside all node spans", () => {
    fc.assert(
      fc.property(
        fc.array(
          fc.record({
            startLine: fc.integer({ min: 5, max: 10 }),
            endLine: fc.integer({ min: 5, max: 10 }),
            startCol: fc.integer({ min: 1, max: 20 }),
            endCol: fc.integer({ min: 1, max: 20 }),
          }).map((r): SpanNodeSpec => ({
            startLine: Math.min(r.startLine, r.endLine),
            endLine: Math.max(r.startLine, r.endLine),
            startCol: r.startCol,
            endCol: r.endCol,
          })),
          { minLength: 1, maxLength: 10 },
        ),
        (specs) => {
          const graph = buildSpanGraph(specs);
          // Query line 100 is guaranteed outside all spans (max endLine = 10)
          const result = getNodesByLine(graph, 100);
          expect(result).toEqual([]);
        },
      ),
      { numRuns: 100 },
    );
  });
});
