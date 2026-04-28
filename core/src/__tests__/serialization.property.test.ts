import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { Node } from "../node.js";
import { ProofGraph } from "../proof-graph.js";
import {
  serializeProofGraph,
  deserializeProofGraph,
} from "../serialization.js";

/**
 * Property 1: ProofGraph JSON round-trip
 * Validates: Requirements 1.4, 3.7
 *
 * For any valid ProofGraph, serializing to JSON then deserializing
 * then re-serializing SHALL produce identical JSON output.
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

/** Generator: a single Node */
const arbNodeParams = fc.record({
  file: arbFileName,
  sLine: arbLine,
  sCol: arbCol,
  eLine: arbLine,
  eCol: arbCol,
  prooftext: arbProoftext,
  isTopAssertion: fc.boolean(),
});

/** Generator: a valid ProofGraph with random nodes, top nodes, and edges */
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

    // Generate which nodes are top nodes and random edges between existing nodes
    return fc
      .record({
        topIndices: fc.array(fc.integer({ min: 0, max: nodeCount - 1 }), {
          minLength: 0,
          maxLength: nodeCount,
        }),
        edges: fc.array(
          fc.record({
            from: fc.integer({ min: 0, max: nodeCount - 1 }),
            to: fc.integer({ min: 0, max: nodeCount - 1 }),
          }),
          { minLength: 0, maxLength: nodeCount * 2 },
        ),
      })
      .map(({ topIndices, edges }) => {
        const graph = new ProofGraph();

        // Add nodes
        const nodes: Node[] = uniqueParams.map(
          (p) =>
            new Node(
              p.file,
              p.sLine,
              p.sCol,
              p.eLine,
              p.eCol,
              p.prooftext,
              p.isTopAssertion,
            ),
        );
        for (const node of nodes) {
          graph.addNode(node);
        }

        // Add top nodes (deduplicated)
        const topSet = new Set(topIndices);
        for (const idx of topSet) {
          graph.addTopNode(nodes[idx]);
        }

        // Add edges (skip self-loops, deduplicate)
        const edgeSet = new Set<string>();
        for (const e of edges) {
          if (e.from !== e.to) {
            const key = `${e.from}-${e.to}`;
            if (!edgeSet.has(key)) {
              edgeSet.add(key);
              graph.addEdge(nodes[e.from].id, nodes[e.to].id);
            }
          }
        }

        return graph;
      });
  });

describe("Property 1: ProofGraph JSON round-trip", () => {
  it("serialize → deserialize → re-serialize produces identical JSON", () => {
    fc.assert(
      fc.property(arbProofGraph, (graph) => {
        const json1 = serializeProofGraph(graph);
        const restored = deserializeProofGraph(json1);
        const json2 = serializeProofGraph(restored);
        expect(json2).toBe(json1);
      }),
      { numRuns: 200 },
    );
  });
});
