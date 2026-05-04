import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { parseProof } from "../../../core/src/proof.js";
import { CovStatus, TokenType } from "../../../core/src/types.js";
import { Node } from "../../../core/src/node.js";
import { ProofGraph } from "../../../core/src/proof-graph.js";

/**
 * Property 4: CovStatusInternal follows BFS reachability from top assertions
 * Validates: Requirements 3.3
 *
 * For any ProofGraph after setCoverageStatus:
 * - A node reachable via BFS from a Postcondition top node → CovStatusInternal = CovComplete
 * - A node reachable only from non-Postcondition top nodes → CovStatusInternal = CovTest
 * - Unreachable nodes → CovStatusInternal = Uncovered
 */

const POSTCONDITION_TEXT = "this postcondition holds";
const PRECONDITION_TEXT = "method requires clause foo";
const CODELINE_TEXT = "some code line";
const FILE = "test.dfy";

interface TopNodeSpec {
  line: number;
  isPostcondition: boolean;
  childLines: number[];
}

/**
 * Generator: a graph config with top nodes and their children.
 * Each top node has a unique line. Children are non-top code line nodes.
 * Some child lines may be shared across tops (testing overlap).
 * Some lines are orphans (not connected to any top).
 */
const arbGraphConfig = fc
  .integer({ min: 1, max: 6 })
  .chain((topCount) =>
    fc.integer({ min: 0, max: 8 }).chain((childPoolSize) => {
      const topLines = Array.from({ length: topCount }, (_, i) => i + 1);
      const childLines = Array.from(
        { length: childPoolSize },
        (_, i) => topCount + i + 1,
      );
      const orphanStart = topCount + childPoolSize + 1;

      return fc
        .record({
          topSpecs: fc.tuple(
            ...topLines.map((line) =>
              fc.record({
                line: fc.constant(line),
                isPostcondition: fc.boolean(),
                childLines: fc.subarray(childLines, { minLength: 0 }),
              }),
            ),
          ),
          orphanCount: fc.integer({ min: 0, max: 4 }),
        })
        .map(({ topSpecs, orphanCount }) => ({
          tops: topSpecs as TopNodeSpec[],
          childLines,
          orphanLines: Array.from(
            { length: orphanCount },
            (_, i) => orphanStart + i,
          ),
        }));
    }),
  );

/**
 * Build a synthetic prover log from the config.
 */
function buildLog(config: {
  tops: TopNodeSpec[];
  orphanLines: number[];
}): string {
  const lines: string[] = [];

  config.tops.forEach((top, batchIdx) => {
    const prooftext = top.isPostcondition
      ? POSTCONDITION_TEXT
      : PRECONDITION_TEXT;

    lines.push(`  Assertion batch ${batchIdx}:`);
    lines.push(`  Assertions:`);
    lines.push(
      `    ${FILE}(${top.line}, 1)-(${top.line}, 10): ${prooftext}`,
    );

    if (top.childLines.length > 0) {
      lines.push(`  Proof dependencies:`);
      for (const cl of top.childLines) {
        lines.push(
          `    ${FILE}(${cl}, 1)-(${cl}, 10): ${CODELINE_TEXT}`,
        );
      }
    }
  });

  return lines.join("\n");
}

/**
 * Compute expected CovStatusInternal independently via BFS.
 */
function computeExpected(
  graph: ProofGraph,
): Map<string, CovStatus> {
  const expected = new Map<string, CovStatus>();
  for (const n of graph.getAllNodes()) {
    expected.set(n.id, CovStatus.Uncovered);
  }

  // Phase 1: Postcondition tops → CovComplete for self + all BFS provedBy reachable
  const postTops = graph
    .getAllTopNodes()
    .filter((t) => t.type === TokenType.Postcondition);
  for (const post of postTops) {
    expected.set(post.id, CovStatus.CovComplete);
    const neighbors = graph.getBFSNeighbors(post.id, true, false);
    if (neighbors) {
      for (const r of neighbors) {
        expected.set(r.node.id, CovStatus.CovComplete);
      }
    }
  }

  // Phase 2: Non-postcondition tops
  // - No children → stays Uncovered
  // - Non-manual → self CovComplete
  // - Manual → self CovComplete only if any child is already CovComplete
  // - Children: CovComplete for auto assertion tops, CovTest otherwise (if not already CovComplete)
  const nonPostTops = graph
    .getAllTopNodes()
    .filter((t) => t.type !== TokenType.Postcondition);
  for (const top of nonPostTops) {
    const neighbors = graph.getBFSNeighbors(top.id, true, false);
    const hasChildren = neighbors != null && neighbors.length > 0;

    if (!hasChildren) {
      continue;
    }

    if (top.type !== TokenType.AssertionManual) {
      expected.set(top.id, CovStatus.CovComplete);
    }

    if (neighbors) {
      for (const r of neighbors) {
        if (expected.get(r.node.id) === CovStatus.CovComplete) {
          expected.set(top.id, CovStatus.CovComplete);
        }
        if (expected.get(r.node.id) !== CovStatus.CovComplete) {
          if (top.type === TokenType.AssertionAutomatic) {
            expected.set(r.node.id, CovStatus.CovComplete);
          } else {
            expected.set(r.node.id, CovStatus.CovTest);
          }
        }
      }
    }
  }

  return expected;
}

describe("Property 4: CovStatusInternal follows BFS reachability from top assertions", () => {
  it("CovStatusInternal matches BFS reachability rules for all generated graphs", () => {
    fc.assert(
      fc.property(arbGraphConfig, (config) => {
        const maxLine = Math.max(
          ...config.tops.map((t) => t.line),
          ...config.tops.flatMap((t) => t.childLines),
          ...config.orphanLines,
          1,
        );
        const sourceCode = Array.from(
          { length: maxLine },
          (_, i) => `line ${i + 1}`,
        ).join("\n");

        const log = buildLog(config);
        const proof = parseProof(sourceCode, log);

        // Compute expected independently
        const expected = computeExpected(proof.proofGraph);

        // Verify every node
        for (const node of proof.proofGraph.getAllNodes()) {
          const exp = expected.get(node.id);
          expect(node.covStatusInternal).toBe(exp);
        }

        // Verify orphan nodes are not in the graph (parser won't create them
        // since they're not in the log) — orphans by definition aren't parsed.
        // The property still holds: any node NOT in the graph is implicitly Uncovered.
      }),
      { numRuns: 200 },
    );
  });
});

/**
 * Property 5: CovStatus follows token-class policies
 * Validates: Requirements 3.4
 *
 * For any ProofGraph with CovStatusInternal computed, CovStatus SHALL satisfy:
 * - AssertionAutomatic nodes are always CovComplete
 * - AssertionManual nodes are CovComplete only if CovStatusInternal is CovComplete, else Uncovered
 * - CodeLine and Precondition nodes equal their CovStatusInternal
 * - Postcondition top nodes follow the alias/parent/child policy (at minimum: if no children are CovComplete → Uncovered)
 * - Non-top Postcondition nodes equal their CovStatusInternal
 */

const MANUAL_ASSERTION_TEXT = "assertion always holds";
const AUTO_ASSERTION_TEXTS = [
  "index in range",
  "target object is never null",
];

interface TopNodeSpec5 {
  line: number;
  prooftext: string;
  childSpecs: { line: number; prooftext: string }[];
}

/**
 * Generator for Property 5: produces graphs with mixed token types.
 * Top nodes can be postconditions, preconditions, or auto assertions.
 * Children can be code lines, manual assertions, or auto assertions.
 */
const arbGraphConfig5 = fc
  .integer({ min: 1, max: 5 })
  .chain((topCount) =>
    fc.integer({ min: 0, max: 6 }).chain((childPoolSize) => {
      const topLines = Array.from({ length: topCount }, (_, i) => i + 1);
      const childStartLine = topCount + 1;

      const topProoftextArb = fc.oneof(
        fc.constant(POSTCONDITION_TEXT),
        fc.constant(PRECONDITION_TEXT),
      );

      const childProoftextArb = fc.oneof(
        fc.constant(CODELINE_TEXT),
        fc.constant(MANUAL_ASSERTION_TEXT),
        fc.constant(AUTO_ASSERTION_TEXTS[0]),
      );

      // Generate child specs with unique lines
      const childSpecsArb =
        childPoolSize === 0
          ? fc.constant([] as { line: number; prooftext: string }[])
          : fc.tuple(
              ...Array.from({ length: childPoolSize }, (_, i) =>
                childProoftextArb.map((pt) => ({
                  line: childStartLine + i,
                  prooftext: pt,
                })),
              ),
            );

      return fc
        .tuple(
          fc.tuple(
            ...topLines.map((line) =>
              fc.tuple(topProoftextArb, fc.subarray(
                Array.from({ length: childPoolSize }, (_, i) => i),
                { minLength: 0 },
              )).map(([pt, childIndices]) => ({
                line,
                prooftext: pt,
                childIndices,
              })),
            ),
          ),
          childSpecsArb,
          fc.integer({ min: 0, max: 3 }), // orphan count
        )
        .map(([topSpecs, childSpecs, orphanCount]) => {
          const tops: TopNodeSpec5[] = topSpecs.map((ts) => ({
            line: ts.line,
            prooftext: ts.prooftext,
            childSpecs: ts.childIndices
              .filter((i: number) => i < childSpecs.length)
              .map((i: number) => childSpecs[i]),
          }));
          const orphanStart = childStartLine + childPoolSize;
          return {
            tops,
            orphanLines: Array.from(
              { length: orphanCount },
              (_, i) => orphanStart + i,
            ),
          };
        });
    }),
  );

/**
 * Build a prover log from the Property 5 config.
 */
function buildLog5(config: {
  tops: TopNodeSpec5[];
  orphanLines: number[];
}): string {
  const lines: string[] = [];

  config.tops.forEach((top, batchIdx) => {
    lines.push(`  Assertion batch ${batchIdx}:`);
    lines.push(`  Assertions:`);
    lines.push(
      `    ${FILE}(${top.line}, 1)-(${top.line}, 10): ${top.prooftext}`,
    );

    if (top.childSpecs.length > 0) {
      lines.push(`  Proof dependencies:`);
      for (const child of top.childSpecs) {
        lines.push(
          `    ${FILE}(${child.line}, 1)-(${child.line}, 10): ${child.prooftext}`,
        );
      }
    }
  });

  return lines.join("\n");
}

/**
 * Compute expected CovStatus per node based on token-class policies.
 * This mirrors the logic in proof.ts setCoverageStatus but computed independently.
 */
function computeExpectedCovStatus(
  graph: ProofGraph,
): Map<string, CovStatus> {
  const result = new Map<string, CovStatus>();

  for (const node of graph.getAllNodes()) {
    switch (node.type) {
      case TokenType.AssertionAutomatic:
        // Always CovComplete
        result.set(node.id, CovStatus.CovComplete);
        break;

      case TokenType.AssertionManual:
        // CovComplete only if internal is CovComplete, else Uncovered
        result.set(
          node.id,
          node.covStatusInternal === CovStatus.CovComplete
            ? CovStatus.CovComplete
            : CovStatus.Uncovered,
        );
        break;

      case TokenType.CodeLine:
        // Equals CovStatusInternal
        result.set(node.id, node.covStatusInternal);
        break;

      case TokenType.Precondition:
        // Equals CovStatusInternal
        result.set(node.id, node.covStatusInternal);
        break;

      case TokenType.Postcondition:
        if (node.isTopAssertion) {
          // Top postcondition: alias/parent/child policy
          const neighbors = graph.getBFSNeighbors(node.id, true, true);
          let anyChildCovComplete = false;
          if (neighbors) {
            for (const r of neighbors) {
              if (
                r.node.type !== TokenType.Postcondition &&
                r.node.covStatus === CovStatus.CovComplete
              ) {
                anyChildCovComplete = true;
                break;
              }
            }
          }

          let anyParents = false;
          const postParents = graph.getBFSNeighbors(node.id, false);
          if (postParents && postParents.length > 1) {
            anyParents = true;
          }

          if (anyParents && anyChildCovComplete) {
            result.set(node.id, CovStatus.CovComplete);
          } else if (anyChildCovComplete) {
            result.set(node.id, CovStatus.CovTest);
          } else {
            result.set(node.id, CovStatus.Uncovered);
          }
        } else {
          // Non-top postcondition: equals CovStatusInternal
          result.set(node.id, node.covStatusInternal);
        }
        break;

      default:
        result.set(node.id, node.covStatusInternal);
        break;
    }
  }

  return result;
}

describe("Property 5: CovStatus follows token-class policies", () => {
  it("CovStatus matches token-class policy rules for all generated graphs", () => {
    fc.assert(
      fc.property(arbGraphConfig5, (config) => {
        const maxLine = Math.max(
          ...config.tops.map((t) => t.line),
          ...config.tops.flatMap((t) => t.childSpecs.map((c) => c.line)),
          ...config.orphanLines,
          1,
        );
        const sourceCode = Array.from(
          { length: maxLine },
          (_, i) => `line ${i + 1}`,
        ).join("\n");

        const log = buildLog5(config);
        const proof = parseProof(sourceCode, log);

        // Compute expected covStatus independently using token-class policies
        const expected = computeExpectedCovStatus(proof.proofGraph);

        // Verify every node's covStatus
        for (const node of proof.proofGraph.getAllNodes()) {
          const exp = expected.get(node.id);
          expect(node.covStatus).toBe(exp);
        }
      }),
      { numRuns: 200 },
    );
  });

  it("AssertionAutomatic nodes are always CovComplete regardless of CovStatusInternal", () => {
    fc.assert(
      fc.property(arbGraphConfig5, (config) => {
        const maxLine = Math.max(
          ...config.tops.map((t) => t.line),
          ...config.tops.flatMap((t) => t.childSpecs.map((c) => c.line)),
          ...config.orphanLines,
          1,
        );
        const sourceCode = Array.from(
          { length: maxLine },
          (_, i) => `line ${i + 1}`,
        ).join("\n");

        const log = buildLog5(config);
        const proof = parseProof(sourceCode, log);

        for (const node of proof.proofGraph.getAllNodes()) {
          if (node.type === TokenType.AssertionAutomatic) {
            expect(node.covStatus).toBe(CovStatus.CovComplete);
          }
        }
      }),
      { numRuns: 200 },
    );
  });

  it("AssertionManual nodes are CovComplete only if CovStatusInternal is CovComplete, else Uncovered", () => {
    fc.assert(
      fc.property(arbGraphConfig5, (config) => {
        const maxLine = Math.max(
          ...config.tops.map((t) => t.line),
          ...config.tops.flatMap((t) => t.childSpecs.map((c) => c.line)),
          ...config.orphanLines,
          1,
        );
        const sourceCode = Array.from(
          { length: maxLine },
          (_, i) => `line ${i + 1}`,
        ).join("\n");

        const log = buildLog5(config);
        const proof = parseProof(sourceCode, log);

        for (const node of proof.proofGraph.getAllNodes()) {
          if (node.type === TokenType.AssertionManual) {
            if (node.covStatusInternal === CovStatus.CovComplete) {
              expect(node.covStatus).toBe(CovStatus.CovComplete);
            } else {
              expect(node.covStatus).toBe(CovStatus.Uncovered);
            }
          }
        }
      }),
      { numRuns: 200 },
    );
  });

  it("CodeLine and Precondition nodes have covStatus equal to covStatusInternal", () => {
    fc.assert(
      fc.property(arbGraphConfig5, (config) => {
        const maxLine = Math.max(
          ...config.tops.map((t) => t.line),
          ...config.tops.flatMap((t) => t.childSpecs.map((c) => c.line)),
          ...config.orphanLines,
          1,
        );
        const sourceCode = Array.from(
          { length: maxLine },
          (_, i) => `line ${i + 1}`,
        ).join("\n");

        const log = buildLog5(config);
        const proof = parseProof(sourceCode, log);

        for (const node of proof.proofGraph.getAllNodes()) {
          if (
            node.type === TokenType.CodeLine ||
            node.type === TokenType.Precondition
          ) {
            expect(node.covStatus).toBe(node.covStatusInternal);
          }
        }
      }),
      { numRuns: 200 },
    );
  });

  it("Postcondition top nodes with no CovComplete children are Uncovered", () => {
    fc.assert(
      fc.property(arbGraphConfig5, (config) => {
        const maxLine = Math.max(
          ...config.tops.map((t) => t.line),
          ...config.tops.flatMap((t) => t.childSpecs.map((c) => c.line)),
          ...config.orphanLines,
          1,
        );
        const sourceCode = Array.from(
          { length: maxLine },
          (_, i) => `line ${i + 1}`,
        ).join("\n");

        const log = buildLog5(config);
        const proof = parseProof(sourceCode, log);

        for (const node of proof.proofGraph.getAllNodes()) {
          if (
            node.type === TokenType.Postcondition &&
            node.isTopAssertion
          ) {
            const neighbors = proof.proofGraph.getBFSNeighbors(
              node.id,
              true,
              true,
            );
            const anyChildCovComplete =
              neighbors?.some(
                (r) =>
                  r.node.type !== TokenType.Postcondition &&
                  r.node.covStatus === CovStatus.CovComplete,
              ) ?? false;

            if (!anyChildCovComplete) {
              expect(node.covStatus).toBe(CovStatus.Uncovered);
            }
          }
        }
      }),
      { numRuns: 200 },
    );
  });

  it("Non-top Postcondition nodes have covStatus equal to covStatusInternal", () => {
    fc.assert(
      fc.property(arbGraphConfig5, (config) => {
        const maxLine = Math.max(
          ...config.tops.map((t) => t.line),
          ...config.tops.flatMap((t) => t.childSpecs.map((c) => c.line)),
          ...config.orphanLines,
          1,
        );
        const sourceCode = Array.from(
          { length: maxLine },
          (_, i) => `line ${i + 1}`,
        ).join("\n");

        const log = buildLog5(config);
        const proof = parseProof(sourceCode, log);

        for (const node of proof.proofGraph.getAllNodes()) {
          if (
            node.type === TokenType.Postcondition &&
            !node.isTopAssertion
          ) {
            expect(node.covStatus).toBe(node.covStatusInternal);
          }
        }
      }),
      { numRuns: 200 },
    );
  });
});
