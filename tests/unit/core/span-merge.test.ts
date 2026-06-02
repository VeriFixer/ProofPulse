import { describe, it, expect } from "vitest";
import {
  getMessageClass,
  messagesMatch,
  isContained,
  findTightestSpan,
  parseProof,
} from "../../../core/src/proof.js";
import type { SpanEntry, SpanMap } from "../../../core/src/proof.js";

describe("getMessageClass", () => {
  it("postcondition class", () => {
    expect(getMessageClass("this postcondition holds")).toBe("postcondition");
  });

  it("precondition class", () => {
    expect(getMessageClass("the precondition always holds")).toBe("precondition");
  });

  it("loop-invariant class (holds on entry)", () => {
    expect(getMessageClass("this loop invariant holds on entry")).toBe("loop-invariant");
  });

  it("loop-invariant class (maintained by loop)", () => {
    expect(getMessageClass("this loop invariant is maintained by the loop")).toBe("loop-invariant");
  });

  it("exact class for assertion always holds", () => {
    expect(getMessageClass("assertion always holds")).toBe("exact");
  });

  it("exact class for index in range", () => {
    expect(getMessageClass("index in range")).toBe("exact");
  });

  it("exact class for target object is never null", () => {
    expect(getMessageClass("target object is never null")).toBe("exact");
  });
});

describe("messagesMatch", () => {
  describe("postcondition class", () => {
    it("matches ensures clause", () => {
      expect(messagesMatch("this postcondition holds", "ensures clause")).toBe(true);
    });

    it("does not match other messages", () => {
      expect(messagesMatch("this postcondition holds", "assertion always holds")).toBe(false);
      expect(messagesMatch("this postcondition holds", "requires clause at foo")).toBe(false);
    });
  });

  describe("precondition class", () => {
    it("matches requires clause at ...", () => {
      expect(messagesMatch("the precondition always holds", "requires clause at foo.dfy(2,12)-(2,16) from call")).toBe(true);
    });

    it("does not match ensures clause", () => {
      expect(messagesMatch("the precondition always holds", "ensures clause")).toBe(false);
    });
  });

  describe("loop-invariant class", () => {
    it("holds on entry matches loop invariant always holds", () => {
      expect(messagesMatch("this loop invariant holds on entry", "loop invariant always holds")).toBe(true);
    });

    it("maintained by loop matches loop invariant always holds", () => {
      expect(messagesMatch("this loop invariant is maintained by the loop", "loop invariant always holds")).toBe(true);
    });

    it("does not match other messages", () => {
      expect(messagesMatch("this loop invariant holds on entry", "ensures clause")).toBe(false);
    });
  });

  describe("exact class", () => {
    it("matches identical messages", () => {
      expect(messagesMatch("assertion always holds", "assertion always holds")).toBe(true);
      expect(messagesMatch("index in range", "index in range")).toBe(true);
    });

    it("does not match different messages", () => {
      expect(messagesMatch("assertion always holds", "index in range")).toBe(false);
    });

    it("trims whitespace", () => {
      expect(messagesMatch("assertion always holds", "  assertion always holds  ")).toBe(true);
    });
  });
});

describe("isContained", () => {
  it("point at span start is contained", () => {
    expect(isContained(3, 15, 3, 15, 3, 19)).toBe(true);
  });

  it("point at span end is contained", () => {
    expect(isContained(2, 15, 2, 13, 2, 15)).toBe(true);
  });

  it("point inside single-line span", () => {
    expect(isContained(3, 16, 3, 15, 3, 19)).toBe(true);
  });

  it("point before start col on same line", () => {
    expect(isContained(3, 14, 3, 15, 3, 19)).toBe(false);
  });

  it("point after end col on same line", () => {
    expect(isContained(3, 20, 3, 15, 3, 19)).toBe(false);
  });

  it("point on middle line of multi-line span (any col)", () => {
    expect(isContained(5, 999, 3, 15, 7, 2)).toBe(true);
  });

  it("point before span start line", () => {
    expect(isContained(2, 15, 3, 15, 7, 2)).toBe(false);
  });

  it("point after span end line", () => {
    expect(isContained(8, 1, 3, 15, 7, 2)).toBe(false);
  });
});

describe("findTightestSpan", () => {
  const spanMap: SpanMap = [
    { file: "test.dfy", startLine: 3, startCol: 11, endLine: 3, endCol: 19, message: "ensures clause" },
    { file: "test.dfy", startLine: 3, startCol: 5, endLine: 3, endCol: 25, message: "ensures clause" },
    { file: "other.dfy", startLine: 3, startCol: 11, endLine: 3, endCol: 19, message: "ensures clause" },
  ];

  it("returns tightest matching span", () => {
    const result = findTightestSpan(spanMap, "test.dfy", 3, 15, "this postcondition holds");
    expect(result).not.toBeNull();
    expect(result!.startCol).toBe(11);
    expect(result!.endCol).toBe(19);
  });

  it("returns null when file doesn't match", () => {
    const result = findTightestSpan(spanMap, "nope.dfy", 3, 15, "this postcondition holds");
    expect(result).toBeNull();
  });

  it("returns null when message class doesn't match", () => {
    const result = findTightestSpan(spanMap, "test.dfy", 3, 15, "the precondition always holds");
    expect(result).toBeNull();
  });

  it("returns null when point is outside all spans", () => {
    const result = findTightestSpan(spanMap, "test.dfy", 3, 2, "this postcondition holds");
    expect(result).toBeNull();
  });
});

describe("Span merge integration (strict mode)", () => {
  it("postcondition point promoted to ensures clause range", () => {
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(3, 15): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(3, 11)-(3, 19): ensures clause",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes.length).toBe(1);
    expect(topNodes[0].locationId).toBe("test.dfy|||3,11-3,19");
    expect(topNodes[0].prooftext).toBe("this postcondition holds");
  });

  it("precondition point promoted to requires clause range", () => {
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(10, 24): the precondition always holds",
      "  Proof dependencies:",
      "    test.dfy(10, 5)-(10, 31): requires clause at foo.dfy(2,12)-(2,16) from call",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes.length).toBe(1);
    expect(topNodes[0].locationId).toBe("test.dfy|||10,5-10,31");
  });

  it("loop invariant point promoted to loop invariant always holds range", () => {
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(29, 21): this loop invariant holds on entry",
      "  Proof dependencies:",
      "    test.dfy(29, 15)-(29, 30): loop invariant always holds",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes.length).toBe(1);
    expect(topNodes[0].locationId).toBe("test.dfy|||29,15-29,30");
  });

  it("exact match: assertion always holds", () => {
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(8, 3): assertion always holds",
      "  Proof dependencies:",
      "    test.dfy(8, 3)-(8, 25): assertion always holds",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes.length).toBe(1);
    expect(topNodes[0].locationId).toBe("test.dfy|||8,3-8,25");
  });

  it("throws in strict mode when no matching span exists", () => {
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(5, 10): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(99, 1)-(99, 5): ensures clause",
    ].join("\n");

    expect(() => parseProof("", log)).toThrow(/STRICT_SPAN_MERGE/);
  });

  it("range-only top assertion is unchanged", () => {
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(3, 11)-(3, 19): this postcondition holds",
      "  Proof dependencies:",
      "    test.dfy(3, 11)-(3, 19): ensures clause",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes.length).toBe(1);
    expect(topNodes[0].locationId).toBe("test.dfy|||3,11-3,19");
  });
});

import { TokenType } from "../../../core/src/types.js";

describe("Loop invariant classification from real prover logs", () => {
  it("forall loop invariant top assertion classifies as LoopInvariant", () => {
    const log = [
      "  Assertion batch 5:",
      "  Assertions:",
      "    test_index_in_range.dfy(10, 19): this loop invariant holds on entry",
      "  Proof dependencies:",
      "    test_index_in_range.dfy(7,9)-(7,15): assignment (or return)",
      "    test_index_in_range.dfy(10,19)-(10,58): loop invariant always holds",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes.length).toBe(1);
    expect(topNodes[0].getType()).toBe(TokenType.LoopInvariant);
    // Should be promoted to range
    expect(topNodes[0].locationId).toBe("test_index_in_range.dfy|||10,19-10,58");
  });

  it("simple loop invariant (0 <= i <= n.Length) classifies as LoopInvariant", () => {
    const log = [
      "  Assertion batch 3:",
      "  Assertions:",
      "    test_index_in_range.dfy(9, 21): this loop invariant holds on entry",
      "  Proof dependencies:",
      "    test_index_in_range.dfy(7,9)-(7,15): assignment (or return)",
      "    test_index_in_range.dfy(9,19)-(9,24): loop invariant always holds",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes.length).toBe(1);
    expect(topNodes[0].getType()).toBe(TokenType.LoopInvariant);
  });

  it("loop invariant maintained by loop classifies as LoopInvariant", () => {
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(9, 21): this loop invariant is maintained by the loop",
      "  Proof dependencies:",
      "    test.dfy(9,19)-(9,30): loop invariant always holds",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes[0].getType()).toBe(TokenType.LoopInvariant);
  });

  it("range node with message 'loop invariant always holds' classifies as LoopInvariant when top", () => {
    // When a range node is directly in Assertions block
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(9, 19)-(9, 24): loop invariant always holds",
      "  Proof dependencies:",
      "    test.dfy(7,9)-(7,15): assignment (or return)",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes[0].getType()).toBe(TokenType.LoopInvariant);
  });

  it("'array is never null' classifies as AssertionAutomatic", () => {
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(12, 9): array is never null",
      "  Proof dependencies:",
      "    test.dfy(12,9)-(12,9): array is never null",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes[0].getType()).toBe(TokenType.AssertionAutomatic);
  });

  it("range node with prooftext 'loop invariant' promoted to top classifies as LoopInvariant", () => {
    // This is the real scenario: point top assertion gets promoted to a range node
    // whose prooftext is just "loop invariant" (from the Unused/ProofDep block)
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(10, 19): this loop invariant holds on entry",
      "  Proof dependencies:",
      "    test.dfy(10,19)-(10,58): loop invariant always holds",
      "  Unused by proof:",
      "    test.dfy(10,19)-(10,58): loop invariant",
    ].join("\n");

    const proof = parseProof("", log);
    // The promoted top should be LoopInvariant
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes.length).toBe(1);
    expect(topNodes[0].getType()).toBe(TokenType.LoopInvariant);
  });

  it("standalone range node with exact prooftext 'loop invariant' as top classifies as LoopInvariant", () => {
    // When the range node with message "loop invariant" becomes the top via replaceTopNode
    const log = [
      "  Assertion batch 0:",
      "  Assertions:",
      "    test.dfy(10, 19)-(10, 58): loop invariant",
      "  Proof dependencies:",
      "    test.dfy(7,9)-(7,15): assignment (or return)",
    ].join("\n");

    const proof = parseProof("", log);
    const topNodes = proof.proofGraph.getAllTopNodes();
    expect(topNodes[0].getType()).toBe(TokenType.LoopInvariant);
  });
});
