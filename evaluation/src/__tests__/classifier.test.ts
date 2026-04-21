import { describe, it, expect } from "vitest";
import { classifyPostcondition, classifyPrecondition, classifyInvariant, classifySpec } from "../classifier.js";
import { TokenType, CovStatus, type NodeData } from "@proofpulse/core";

function makeNode(type: TokenType, covStatus: CovStatus, line = 1, prooftext = ""): NodeData {
  return {
    id: `node-${line}`, file: "test.dfy",
    start: { line, col: 0 }, end: { line, col: 10 },
    prooftext, isTopAssertion: false, type, covStatus, covStatusInternal: covStatus,
  };
}

describe("classifyPostcondition", () => {
  it("none when no postconditions", () => {
    expect(classifyPostcondition([makeNode(TokenType.CodeLine, CovStatus.CovComplete)])).toBe("none");
  });
  it("strong when post covered and body complete", () => {
    expect(classifyPostcondition([
      makeNode(TokenType.Postcondition, CovStatus.CovComplete, 1),
      makeNode(TokenType.CodeLine, CovStatus.CovComplete, 2),
    ])).toBe("strong");
  });
  it("weak when post uncovered", () => {
    expect(classifyPostcondition([
      makeNode(TokenType.Postcondition, CovStatus.Uncovered, 1),
      makeNode(TokenType.CodeLine, CovStatus.CovComplete, 2),
    ])).toBe("weak");
  });
  it("ignores precondition coverage", () => {
    expect(classifyPostcondition([
      makeNode(TokenType.Postcondition, CovStatus.CovComplete, 1),
      makeNode(TokenType.Precondition, CovStatus.Uncovered, 2),
    ])).toBe("strong");
  });
});

describe("classifyPrecondition", () => {
  it("none when no preconditions", () => {
    expect(classifyPrecondition([])).toBe("none");
  });
  it("required when all covered", () => {
    expect(classifyPrecondition([
      makeNode(TokenType.Precondition, CovStatus.CovComplete, 1),
    ])).toBe("required");
  });
  it("optional when any uncovered", () => {
    expect(classifyPrecondition([
      makeNode(TokenType.Precondition, CovStatus.CovComplete, 1),
      makeNode(TokenType.Precondition, CovStatus.Uncovered, 2),
    ])).toBe("optional");
  });
  it("optional when all uncovered", () => {
    expect(classifyPrecondition([
      makeNode(TokenType.Precondition, CovStatus.Uncovered, 1),
    ])).toBe("optional");
  });
});

describe("classifyInvariant", () => {
  it("none when no invariants", () => {
    expect(classifyInvariant([])).toBe("none");
  });
  it("strong when all invariant nodes covered", () => {
    expect(classifyInvariant([
      makeNode(TokenType.CodeLine, CovStatus.CovComplete, 1, "loop invariant always holds"),
    ])).toBe("strong");
  });
  it("weak when any invariant uncovered", () => {
    expect(classifyInvariant([
      makeNode(TokenType.CodeLine, CovStatus.CovComplete, 1, "loop invariant always holds"),
      makeNode(TokenType.CodeLine, CovStatus.Uncovered, 2, "loop invariant always holds"),
    ])).toBe("weak");
  });
});

describe("classifySpec (overall)", () => {
  it("strong when postcondition strong", () => {
    expect(classifySpec([
      makeNode(TokenType.Postcondition, CovStatus.CovComplete, 1),
    ])).toBe("strong");
  });
  it("weak when no postconditions", () => {
    expect(classifySpec([])).toBe("weak");
  });
});
