import { describe, it, expect } from "vitest";
import { parseProof } from "../../../core/src/proof.js";

/**
 * Integration tests for span merging using realistic multi-batch prover logs.
 * Validates Requirements 4.1, 4.2, 4.3, 4.4
 */

// Realistic prover log with multiple assertion batches, mixed point/range entries
const MULTI_BATCH_LOG = `
  Assertion batch 0:
  Assertions:
    test.dfy(3, 15): this postcondition holds
  Proof dependencies:
    test.dfy(3, 11)-(3, 19): ensures clause
    test.dfy(5, 1)-(5, 10): some code line

  Assertion batch 1:
  Assertions:
    test.dfy(10, 24): the precondition always holds
  Proof dependencies:
    test.dfy(10, 5)-(10, 31): requires clause at helper.dfy(2,12)-(2,16) from call
    test.dfy(8, 1)-(8, 20): assertion always holds

  Assertion batch 2:
  Assertions:
    test.dfy(29, 21): this loop invariant holds on entry
  Proof dependencies:
    test.dfy(29, 15)-(29, 30): loop invariant always holds
    test.dfy(27, 5)-(27, 15): index in range

  Assertion batch 3:
  Assertions:
    test.dfy(40, 3): assertion always holds
  Proof dependencies:
    test.dfy(40, 3)-(40, 25): assertion always holds
    test.dfy(38, 1)-(38, 10): some dep
`;

describe("Span merge integration: multi-batch log", () => {
  it("parses without throwing in strict mode", () => {
    expect(() => parseProof("", MULTI_BATCH_LOG)).not.toThrow();
  });

  it("promotes all point-only top assertions to full ranges", () => {
    const proof = parseProof("", MULTI_BATCH_LOG);
    const topNodes = proof.proofGraph.getAllTopNodes();
    const topIds = topNodes.map((n) => n.id);

    // Batch 0: postcondition promoted
    expect(topIds).toContain("test.dfy:3,11-3,19");
    // Batch 1: precondition promoted
    expect(topIds).toContain("test.dfy:10,5-10,31");
    // Batch 2: loop invariant promoted
    expect(topIds).toContain("test.dfy:29,15-29,30");
    // Batch 3: exact match promoted
    expect(topIds).toContain("test.dfy:40,3-40,25");
  });

  it("no point-only top nodes remain", () => {
    const proof = parseProof("", MULTI_BATCH_LOG);
    const topNodes = proof.proofGraph.getAllTopNodes();

    for (const node of topNodes) {
      const isPoint = node.start.line === node.end.line && node.start.col === node.end.col;
      // All tops should have been promoted to ranges
      expect(isPoint).toBe(false);
    }
  });

  it("proof dependencies are connected as edges", () => {
    const proof = parseProof("", MULTI_BATCH_LOG);

    // Batch 0: top (3,11)-(3,19) should have edge to (5,1)-(5,10)
    const top0 = proof.proofGraph.getNode("test.dfy:3,11-3,19");
    expect(top0).toBeDefined();
    const top0Children = [...top0!.provedBy].map((n) => n.id);
    expect(top0Children).toContain("test.dfy:5,1-5,10");

    // Batch 3: top (40,3)-(40,25) should have edge to (38,1)-(38,10)
    const top3 = proof.proofGraph.getNode("test.dfy:40,3-40,25");
    expect(top3).toBeDefined();
    const top3Children = [...top3!.provedBy].map((n) => n.id);
    expect(top3Children).toContain("test.dfy:38,1-38,10");
  });

  it("preserves prooftext from original top assertion", () => {
    const proof = parseProof("", MULTI_BATCH_LOG);

    const top0 = proof.proofGraph.getNode("test.dfy:3,11-3,19");
    expect(top0!.prooftext).toBe("this postcondition holds");

    const top1 = proof.proofGraph.getNode("test.dfy:10,5-10,31");
    expect(top1!.prooftext).toBe("the precondition always holds");

    const top2 = proof.proofGraph.getNode("test.dfy:29,15-29,30");
    expect(top2!.prooftext).toBe("this loop invariant holds on entry");
  });
});

// Log where all top assertions already have ranges (no promotion needed)
const RANGE_ONLY_LOG = `
  Assertion batch 0:
  Assertions:
    test.dfy(3, 11)-(3, 19): this postcondition holds
  Proof dependencies:
    test.dfy(5, 1)-(5, 10): some code line

  Assertion batch 1:
  Assertions:
    test.dfy(10, 5)-(10, 31): the precondition always holds
  Proof dependencies:
    test.dfy(8, 1)-(8, 20): assertion always holds
`;

describe("Span merge integration: range-only log (backward compat)", () => {
  it("parses without throwing", () => {
    expect(() => parseProof("", RANGE_ONLY_LOG)).not.toThrow();
  });

  it("top nodes retain their original range IDs", () => {
    const proof = parseProof("", RANGE_ONLY_LOG);
    const topIds = proof.proofGraph.getAllTopNodes().map((n) => n.id);

    expect(topIds).toContain("test.dfy:3,11-3,19");
    expect(topIds).toContain("test.dfy:10,5-10,31");
  });

  it("edges are preserved", () => {
    const proof = parseProof("", RANGE_ONLY_LOG);

    const top0 = proof.proofGraph.getNode("test.dfy:3,11-3,19");
    const children0 = [...top0!.provedBy].map((n) => n.id);
    expect(children0).toContain("test.dfy:5,1-5,10");
  });
});

// Log with unused block entries
const UNUSED_BLOCK_LOG = `
  Assertion batch 0:
  Assertions:
    test.dfy(3, 15): this postcondition holds
  Unused by proof:
    test.dfy(3, 11)-(3, 19): ensures clause
    test.dfy(7, 1)-(7, 8): unused dep
`;

describe("Span merge integration: unused block entries in span map", () => {
  it("span map includes entries from Unused by proof block", () => {
    const proof = parseProof("", UNUSED_BLOCK_LOG);
    const topNodes = proof.proofGraph.getAllTopNodes();
    const topIds = topNodes.map((n) => n.id);

    // Point (3,15) should be promoted using the ensures clause from Unused block
    expect(topIds).toContain("test.dfy:3,11-3,19");
  });
});
