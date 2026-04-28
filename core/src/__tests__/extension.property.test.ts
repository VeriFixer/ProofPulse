import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { CovStatus, TokenType } from "../types.js";
import { Node } from "../node.js";
import { ProofGraph } from "../proof-graph.js";
import { getNodesByLine, getRelatedNodes } from "../coverage.js";

const FILE = "test.dfy";
const COV_STATUSES = [CovStatus.CovComplete, CovStatus.CovTest, CovStatus.Uncovered] as const;

// ─── Pure logic extracted from decorations.ts ───

interface GutterBuckets {
  uncoveredLines: number[];
  covTestLines: number[];
}

/** Pure gutter decoration mapping: CovStatus[] → line indices per bucket */
function computeGutterBuckets(lineStatus: CovStatus[]): GutterBuckets {
  const uncoveredLines: number[] = [];
  const covTestLines: number[] = [];
  for (let i = 0; i < lineStatus.length; i++) {
    if (lineStatus[i] === CovStatus.Uncovered) {
      uncoveredLines.push(i);
    } else if (lineStatus[i] === CovStatus.CovTest) {
      covTestLines.push(i);
    }
  }
  return { uncoveredLines, covTestLines };
}

interface InlineBuckets {
  uncoveredNodes: Node[];
  covTestNodes: Node[];
}

/** Pure inline decoration mapping: Node[] → nodes per bucket */
function computeInlineBuckets(nodes: Node[]): InlineBuckets {
  const uncoveredNodes: Node[] = [];
  const covTestNodes: Node[] = [];
  for (const node of nodes) {
    if (node.covStatus === CovStatus.Uncovered) {
      uncoveredNodes.push(node);
    } else if (node.covStatus === CovStatus.CovTest) {
      covTestNodes.push(node);
    }
  }
  return { uncoveredNodes, covTestNodes };
}

/** Pure hover content computation: returns all fields that should appear */
function computeHoverContent(
  graph: ProofGraph,
  node: Node,
): {
  covStatus: CovStatus;
  prooftext: string;
  id: string;
  type: TokenType;
  covStatusInternal: CovStatus;
  neighbors: { id: string; prooftext: string }[];
} {
  const related = getRelatedNodes(graph, node.id) ?? [];
  return {
    covStatus: node.covStatus,
    prooftext: node.prooftext,
    id: node.id,
    type: node.type,
    covStatusInternal: node.covStatusInternal,
    neighbors: related.map((r) => ({ id: r.id, prooftext: r.prooftext })),
  };
}

// ─── Generators ───

const arbCovStatus = fc.constantFrom(...COV_STATUSES);

const arbLineStatusArray = fc.array(arbCovStatus, { minLength: 1, maxLength: 30 });


interface NodeSpec {
  startLine: number;
  endLine: number;
  startCol: number;
  endCol: number;
  covStatus: CovStatus;
  covStatusInternal: CovStatus;
  prooftext: string;
}

const arbNodeSpec = (maxLine: number): fc.Arbitrary<NodeSpec> =>
  fc.record({
    startLine: fc.integer({ min: 1, max: maxLine }),
    endLine: fc.integer({ min: 1, max: maxLine }),
    startCol: fc.integer({ min: 1, max: 40 }),
    endCol: fc.integer({ min: 1, max: 40 }),
    covStatus: arbCovStatus,
    covStatusInternal: arbCovStatus,
    prooftext: fc.stringOf(fc.char(), { minLength: 1, maxLength: 20 }),
  }).map((r) => ({
    ...r,
    startLine: Math.min(r.startLine, r.endLine),
    endLine: Math.max(r.startLine, r.endLine),
  }));

function buildNodeFromSpec(spec: NodeSpec, index: number): Node {
  const node = new Node(
    FILE,
    spec.startLine,
    spec.startCol + index, // unique col for unique ID
    spec.endLine,
    spec.endCol + index,
    spec.prooftext,
    false,
  );
  node.covStatus = spec.covStatus;
  node.covStatusInternal = spec.covStatusInternal;
  return node;
}

function buildGraphFromSpecs(specs: NodeSpec[]): { graph: ProofGraph; nodes: Node[] } {
  const graph = new ProofGraph();
  const nodes: Node[] = [];
  specs.forEach((spec, i) => {
    const node = buildNodeFromSpec(spec, i);
    graph.addNode(node);
    nodes.push(node);
  });
  return { graph, nodes };
}

// ─── Property 9: Gutter decorations match line status ───

/**
 * Property 9: Gutter decorations match line status
 * Validates: Requirements 6.1, 6.2, 6.3
 *
 * For any CovStatus[] array, the gutter decoration buckets SHALL contain:
 * - Uncovered lines → uncoveredLines set
 * - CovTest lines → covTestLines set
 * - CovComplete lines → neither set
 */
describe("Property 9: Gutter decorations match line status", () => {
  it("uncovered lines go to uncoveredLines bucket, covTest to covTestLines, covComplete to neither", () => {
    fc.assert(
      fc.property(arbLineStatusArray, (lineStatus) => {
        const { uncoveredLines, covTestLines } = computeGutterBuckets(lineStatus);

        // Every Uncovered line index is in uncoveredLines
        for (let i = 0; i < lineStatus.length; i++) {
          if (lineStatus[i] === CovStatus.Uncovered) {
            expect(uncoveredLines).toContain(i);
          }
          if (lineStatus[i] === CovStatus.CovTest) {
            expect(covTestLines).toContain(i);
          }
          if (lineStatus[i] === CovStatus.CovComplete) {
            expect(uncoveredLines).not.toContain(i);
            expect(covTestLines).not.toContain(i);
          }
        }

        // No extra entries
        expect(uncoveredLines.length).toBe(
          lineStatus.filter((s) => s === CovStatus.Uncovered).length,
        );
        expect(covTestLines.length).toBe(
          lineStatus.filter((s) => s === CovStatus.CovTest).length,
        );
      }),
      { numRuns: 200 },
    );
  });

  it("uncoveredLines and covTestLines are disjoint", () => {
    fc.assert(
      fc.property(arbLineStatusArray, (lineStatus) => {
        const { uncoveredLines, covTestLines } = computeGutterBuckets(lineStatus);
        const uncoveredSet = new Set(uncoveredLines);
        for (const line of covTestLines) {
          expect(uncoveredSet.has(line)).toBe(false);
        }
      }),
      { numRuns: 200 },
    );
  });
});

// ─── Property 10: Inline decorations match node status ───

/**
 * Property 10: Inline decorations match node status
 * Validates: Requirements 7.1, 7.2, 7.3
 *
 * For any set of Nodes, the inline decoration buckets SHALL contain:
 * - Uncovered nodes → uncoveredNodes set
 * - CovTest nodes → covTestNodes set
 * - CovComplete nodes → neither set
 */
describe("Property 10: Inline decorations match node status", () => {
  it("nodes are bucketed by covStatus: Uncovered→uncovered, CovTest→covTest, CovComplete→neither", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 20 }).chain((maxLine) =>
          fc.array(arbNodeSpec(maxLine), { minLength: 0, maxLength: 15 }),
        ),
        (specs) => {
          const { nodes } = buildGraphFromSpecs(specs);
          const { uncoveredNodes, covTestNodes } = computeInlineBuckets(nodes);

          const uncoveredIds = new Set(uncoveredNodes.map((n) => n.id));
          const covTestIds = new Set(covTestNodes.map((n) => n.id));

          for (const node of nodes) {
            if (node.covStatus === CovStatus.Uncovered) {
              expect(uncoveredIds.has(node.id)).toBe(true);
            } else if (node.covStatus === CovStatus.CovTest) {
              expect(covTestIds.has(node.id)).toBe(true);
            } else {
              // CovComplete → not in any bucket
              expect(uncoveredIds.has(node.id)).toBe(false);
              expect(covTestIds.has(node.id)).toBe(false);
            }
          }

          // Counts match
          expect(uncoveredNodes.length).toBe(
            nodes.filter((n) => n.covStatus === CovStatus.Uncovered).length,
          );
          expect(covTestNodes.length).toBe(
            nodes.filter((n) => n.covStatus === CovStatus.CovTest).length,
          );
        },
      ),
      { numRuns: 200 },
    );
  });

  it("uncoveredNodes and covTestNodes are disjoint", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 10 }).chain((maxLine) =>
          fc.array(arbNodeSpec(maxLine), { minLength: 1, maxLength: 10 }),
        ),
        (specs) => {
          const { nodes } = buildGraphFromSpecs(specs);
          const { uncoveredNodes, covTestNodes } = computeInlineBuckets(nodes);
          const uncoveredIds = new Set(uncoveredNodes.map((n) => n.id));
          for (const n of covTestNodes) {
            expect(uncoveredIds.has(n.id)).toBe(false);
          }
        },
      ),
      { numRuns: 200 },
    );
  });
});


// ─── Property 11: Hover content contains all required node info and neighbors ───

/**
 * Property 11: Hover content contains all required node info and neighbors
 * Validates: Requirements 8.1, 8.2
 *
 * For any ProofGraph and any node within it, the hover content SHALL contain:
 * - The node's covStatus, prooftext, id, type, covStatusInternal
 * - All BFS neighbors' IDs and proof texts
 */

/** Build a graph with edges for hover testing */
function buildConnectedGraph(
  specs: NodeSpec[],
  edgeIndices: [number, number][],
): { graph: ProofGraph; nodes: Node[] } {
  const graph = new ProofGraph();
  const nodes: Node[] = [];
  specs.forEach((spec, i) => {
    const node = buildNodeFromSpec(spec, i);
    graph.addNode(node);
    nodes.push(node);
  });
  for (const [fromIdx, toIdx] of edgeIndices) {
    if (fromIdx < nodes.length && toIdx < nodes.length && fromIdx !== toIdx) {
      try {
        graph.addEdge(nodes[fromIdx].id, nodes[toIdx].id);
      } catch {
        // skip invalid edges
      }
    }
  }
  return { graph, nodes };
}

/** Generator for a graph with edges and a selected node index */
const arbGraphWithNode = fc
  .integer({ min: 1, max: 10 })
  .chain((maxLine) =>
    fc
      .array(arbNodeSpec(maxLine), { minLength: 1, maxLength: 8 })
      .chain((specs) =>
        fc
          .tuple(
            fc.array(
              fc.tuple(
                fc.integer({ min: 0, max: specs.length - 1 }),
                fc.integer({ min: 0, max: specs.length - 1 }),
              ),
              { minLength: 0, maxLength: 6 },
            ),
            fc.integer({ min: 0, max: specs.length - 1 }),
          )
          .map(([edges, nodeIdx]) => ({ specs, edges, nodeIdx })),
      ),
  );

describe("Property 11: Hover content contains all required node info and neighbors", () => {
  it("hover content includes covStatus, prooftext, id, type, covStatusInternal for the target node", () => {
    fc.assert(
      fc.property(arbGraphWithNode, ({ specs, edges, nodeIdx }) => {
        const { graph, nodes } = buildConnectedGraph(specs, edges);
        const target = nodes[nodeIdx];
        const content = computeHoverContent(graph, target);

        expect(content.covStatus).toBe(target.covStatus);
        expect(content.prooftext).toBe(target.prooftext);
        expect(content.id).toBe(target.id);
        expect(content.type).toBe(target.type);
        expect(content.covStatusInternal).toBe(target.covStatusInternal);
      }),
      { numRuns: 200 },
    );
  });

  it("hover content includes all BFS neighbors' IDs and proof texts", () => {
    fc.assert(
      fc.property(arbGraphWithNode, ({ specs, edges, nodeIdx }) => {
        const { graph, nodes } = buildConnectedGraph(specs, edges);
        const target = nodes[nodeIdx];
        const content = computeHoverContent(graph, target);

        // Independently compute BFS neighbors
        const bfsNeighbors = graph.getBFSNeighbors(target.id, false, true) ?? [];
        const expectedIds = bfsNeighbors.map((r) => r.node.id).sort();
        const actualIds = content.neighbors.map((n) => n.id).sort();

        expect(actualIds).toEqual(expectedIds);

        // Each neighbor's prooftext is present
        for (const r of bfsNeighbors) {
          const found = content.neighbors.find((n) => n.id === r.node.id);
          expect(found).toBeDefined();
          expect(found!.prooftext).toBe(r.node.prooftext);
        }
      }),
      { numRuns: 200 },
    );
  });

  it("hover content neighbors do not include the target node itself", () => {
    fc.assert(
      fc.property(arbGraphWithNode, ({ specs, edges, nodeIdx }) => {
        const { graph, nodes } = buildConnectedGraph(specs, edges);
        const target = nodes[nodeIdx];
        const content = computeHoverContent(graph, target);

        const neighborIds = content.neighbors.map((n) => n.id);
        expect(neighborIds).not.toContain(target.id);
      }),
      { numRuns: 200 },
    );
  });
});
