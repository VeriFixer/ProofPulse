import { describe, it, expect } from "vitest";
import { classifySpec } from "../classifier";
import { TokenType, CovStatus, type NodeData } from "@proofpulse/core";

function makeNode(
  type: TokenType,
  covStatus: CovStatus,
  line = 1
): NodeData {
  return {
    id: `node-${line}`,
    file: "test.dfy",
    start: { line, col: 0 },
    end: { line, col: 10 },
    prooftext: "",
    isTopAssertion: false,
    type,
    covStatus,
    covStatusInternal: covStatus,
  };
}

describe("classifySpec", () => {
  it("returns weak for empty nodes", () => {
    expect(classifySpec([])).toBe("weak");
  });

  it("returns weak when no postconditions exist", () => {
    const nodes = [makeNode(TokenType.CodeLine, CovStatus.CovComplete)];
    expect(classifySpec(nodes)).toBe("weak");
  });

  it("returns strong when postconditions covered and body complete", () => {
    const nodes = [
      makeNode(TokenType.Postcondition, CovStatus.CovComplete, 1),
      makeNode(TokenType.CodeLine, CovStatus.CovComplete, 2),
    ];
    expect(classifySpec(nodes)).toBe("strong");
  });

  it("returns strong when postcondition has CovTest", () => {
    const nodes = [
      makeNode(TokenType.Postcondition, CovStatus.CovTest, 1),
      makeNode(TokenType.CodeLine, CovStatus.CovComplete, 2),
    ];
    expect(classifySpec(nodes)).toBe("strong");
  });

  it("returns weak when postcondition is uncovered", () => {
    const nodes = [
      makeNode(TokenType.Postcondition, CovStatus.Uncovered, 1),
      makeNode(TokenType.CodeLine, CovStatus.CovComplete, 2),
    ];
    expect(classifySpec(nodes)).toBe("weak");
  });

  it("returns weak when body node is not CovComplete", () => {
    const nodes = [
      makeNode(TokenType.Postcondition, CovStatus.CovComplete, 1),
      makeNode(TokenType.CodeLine, CovStatus.CovTest, 2),
    ];
    expect(classifySpec(nodes)).toBe("weak");
  });

  it("returns weak when body node is uncovered", () => {
    const nodes = [
      makeNode(TokenType.Postcondition, CovStatus.CovComplete, 1),
      makeNode(TokenType.CodeLine, CovStatus.Uncovered, 2),
    ];
    expect(classifySpec(nodes)).toBe("weak");
  });

  it("ignores non-postcondition/codeline node types", () => {
    const nodes = [
      makeNode(TokenType.Postcondition, CovStatus.CovComplete, 1),
      makeNode(TokenType.Precondition, CovStatus.Uncovered, 2),
      makeNode(TokenType.AssertionManual, CovStatus.Uncovered, 3),
    ];
    // No body nodes, postcondition covered → strong
    expect(classifySpec(nodes)).toBe("strong");
  });

  it("returns strong with no body nodes but postconditions covered", () => {
    const nodes = [
      makeNode(TokenType.Postcondition, CovStatus.CovTest, 1),
    ];
    expect(classifySpec(nodes)).toBe("strong");
  });
});
