import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { computeLineStatus } from "../../../core/src/coverage.js";
import { CovStatus } from "../../../core/src/types.js";
import { Node } from "../../../core/src/node.js";
import { ProofGraph } from "../../../core/src/proof-graph.js";

/**
 * Property 6: Line status is worst-case of token statuses
 * Validates: Requirements 4.1
 *
 * For any ProofGraph and source code string, the computed Line_Status for each
 * line SHALL equal the worst-case CovStatus (Uncovered > CovTest > CovComplete)
 * among all nodes whose source span starts on that line, defaulting to
 * CovComplete if no tokens exist on that line.
 *
 * Note: The implementation uses start.line only (not full span range).
 */

const FILE = "test.dfy";
const COV_STATUSES = [CovStatus.CovComplete, CovStatus.CovTest, CovStatus.Uncovered] as const;

/** Worst-case ordering: Uncovered > CovTest > CovComplete */
function worstCase(a: CovStatus, b: CovStatus): CovStatus {
  const rank: Record<CovStatus, number> = {
    [CovStatus.CovComplete]: 0,
    [CovStatus.CovTest]: 1,
    [CovStatus.Uncovered]: 2,
  };
  return rank[a] >= rank[b] ? a : b;
}

/** Arbitrary node spec: a start line (1-based) and a covStatus */
interface NodeSpec {
  startLine: number;
  covStatus: CovStatus;
}

/**
 * Generator: random number of source lines, random nodes placed on those lines
 * with random covStatus values.
 */
const arbScenario = fc
  .integer({ min: 1, max: 20 })
  .chain((lineCount) =>
    fc
      .array(
        fc.record({
          startLine: fc.integer({ min: 1, max: lineCount }),
          covStatus: fc.constantFrom(...COV_STATUSES),
        }),
        { minLength: 0, maxLength: 15 },
      )
      .map((nodes) => ({ lineCount, nodes })),
  );

/** Build a ProofGraph from node specs, setting covStatus directly.
 *  Each node gets a unique column to ensure unique IDs. */
function buildGraph(specs: NodeSpec[]): ProofGraph {
  const graph = new ProofGraph();
  specs.forEach((spec, i) => {
    const col = i + 1; // unique col per node → unique id
    const node = new Node(
      FILE,
      spec.startLine,
      col,
      spec.startLine,
      col + 5,
      `token ${i}`,
      false,
    );
    node.covStatus = spec.covStatus;
    graph.addNode(node);
  });
  return graph;
}

/** Compute expected line statuses independently. */
function computeExpected(lineCount: number, specs: NodeSpec[]): CovStatus[] {
  const result = new Array<CovStatus>(lineCount).fill(CovStatus.CovComplete);
  for (const spec of specs) {
    const idx = Math.max(0, spec.startLine - 1);
    if (idx < lineCount) {
      result[idx] = worstCase(result[idx], spec.covStatus);
    }
  }
  return result;
}

describe("Property 6: Line status is worst-case of token statuses", () => {
  it("computeLineStatus matches independent worst-case computation for all generated scenarios", () => {
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

  it("a single Uncovered node on a line makes that line Uncovered regardless of other nodes", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 10 }).chain((lineCount) =>
          fc
            .integer({ min: 1, max: lineCount })
            .chain((targetLine) =>
              fc
                .array(fc.constantFrom(...COV_STATUSES), {
                  minLength: 0,
                  maxLength: 5,
                })
                .map((otherStatuses) => ({
                  lineCount,
                  targetLine,
                  otherStatuses,
                })),
            ),
        ),
        ({ lineCount, targetLine, otherStatuses }) => {
          const specs: NodeSpec[] = [
            { startLine: targetLine, covStatus: CovStatus.Uncovered },
            ...otherStatuses.map((s) => ({
              startLine: targetLine,
              covStatus: s,
            })),
          ];

          const sourceCode = Array.from(
            { length: lineCount },
            (_, i) => `line ${i + 1}`,
          ).join("\n");

          const graph = buildGraph(specs);
          const actual = computeLineStatus(graph, sourceCode);

          expect(actual[targetLine - 1]).toBe(CovStatus.Uncovered);
        },
      ),
      { numRuns: 100 },
    );
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
    const node = new Node(
      FILE,
      spec.startLine,
      spec.startCol,
      spec.endLine,
      spec.endCol,
      `span token ${i}`,
      false,
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
        const resultIds = result.map((n) => n.id).sort();
        const expectedIds = expected.map((n) => n.id).sort();

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
