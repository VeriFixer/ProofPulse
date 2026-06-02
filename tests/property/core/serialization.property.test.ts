import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { ProofNode } from "../../../core/src/proof-node.js";
import { ProofGraph } from "../../../core/src/proof-graph.js";

/**
 * Property 1: ProofGraph YAML round-trip
 * Validates: Requirements 7.1, 7.2, 7.3
 *
 * For any valid ProofGraph, serializing to YAML then deserializing
 * then re-serializing SHALL produce identical YAML output.
 */

/** Generator: random file name */
const arbFileName = fc
  .stringMatching(/^[a-z][a-z0-9_]{0,9}\.dfy$/)
  .filter((s) => s.length >= 5);

/** Generator: random source location numbers */
const arbLine = fc.integer({ min: 1, max: 500 });
const arbCol = fc.integer({ min: 0, max: 120 });

/** Generator: random prooftext (avoid keyword collisions for simplicity) */
const arbProoftext = fc.string({ minLength: 1, maxLength: 30 });

/** Generator: a single ProofNode params */
const arbNodeParams = fc.record({
  file: arbFileName,
  sLine: arbLine,
  sCol: arbCol,
  eLine: arbLine,
  eCol: arbCol,
  prooftext: arbProoftext,
  isTop: fc.boolean(),
});

/** Generator: a valid ProofGraph with random nodes and edges */
const arbProofGraph = fc
  .record({
    nodeParams: fc.array(arbNodeParams, { minLength: 1, maxLength: 15 }),
  })
  .chain(({ nodeParams }) => {
    // Build nodes, deduplicate by id
    const seen = new Set<string>();
    const uniqueParams: typeof nodeParams = [];
    for (const p of nodeParams) {
      const id = `${p.file}:${p.sLine},${p.sCol}-${p.eLine},${p.eCol}`;
      if (!seen.has(id)) {
        seen.add(id);
        uniqueParams.push(p);
      }
    }
    const nodeCount = uniqueParams.length;

    return fc
      .record({
        edges: fc.array(
          fc.record({
            from: fc.integer({ min: 0, max: nodeCount - 1 }),
            to: fc.integer({ min: 0, max: nodeCount - 1 }),
          }),
          { minLength: 0, maxLength: nodeCount * 2 },
        ),
      })
      .map(({ edges }) => {
        const graph = new ProofGraph();

        const nodes: ProofNode[] = uniqueParams.map(
          (p) =>
            new ProofNode(
              p.file,
              { line: p.sLine, col: p.sCol },
              { line: p.eLine, col: p.eCol },
              "",
              "",
              p.prooftext,
            ),
        );

        for (const node of nodes) {
          graph.addNode(node);
          if (uniqueParams[nodes.indexOf(node)].isTop) {
            node.addRole("isTop");
          }
        }

        // Add provedBy edges (skip self-loops)
        const edgeSet = new Set<string>();
        for (const e of edges) {
          if (e.from !== e.to) {
            const key = `${e.from}-${e.to}`;
            if (!edgeSet.has(key)) {
              edgeSet.add(key);
              graph.addProvedBy(nodes[e.from].getId(), nodes[e.to].getId());
            }
          }
        }

        return graph;
      });
  });

describe("Property 1: ProofGraph YAML round-trip", () => {
  it("serialize → deserialize → re-serialize produces identical YAML", () => {
    fc.assert(
      fc.property(arbProofGraph, (graph) => {
        const yaml1 = graph.toYAML();
        const restored = new ProofGraph();
        restored.fromYAML(yaml1);
        const yaml2 = restored.toYAML();
        expect(yaml2).toBe(yaml1);
      }),
      { numRuns: 200 },
    );
  });
});
