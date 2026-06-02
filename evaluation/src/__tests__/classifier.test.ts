import { describe, it, expect } from "vitest";
import { classifyPostcondition, classifyPrecondition, classifyInvariant, classifySpec } from "../classifier.js";
import { TokenType, CovStatus, type NodeData, ProofNode, ProofGraph } from "@proofpulse/core";

function makeNode(type: TokenType, covStatus: CovStatus, line = 1, prooftext = ""): NodeData {
  return {
    id: `node-${line}`, file: "test.dfy",
    start: { line, col: 0 }, end: { line, col: 10 },
    prooftexts: [prooftext], roles: { isTop: false, isCall: false, isProvedBy: false, isUnused: false }, type, covStatus, covStatusInternal: covStatus,
  };
}

/** Map TokenType to a prooftext that classifyNodeType will resolve correctly. */
function prooftextForType(type: TokenType): string {
  switch (type) {
    case TokenType.Postcondition: return "this postcondition holds";
    case TokenType.Precondition: return "precondition always holds";
    case TokenType.LoopInvariant: return "loop invariant always holds";
    case TokenType.Call: return "ensures clause at foo(1,1)-(1,5)";
    case TokenType.AssertionManual: return "assertion always holds";
    case TokenType.AssertionAutomatic: return "index in range";
    default: return "some code line";
  }
}

/** Build a ProofGraph from specs. Postcondition/LoopInvariant types are added as tops.
 * provedByLines maps a top's line to an array of prover lines (for building edges). */
function buildGraph(specs: { type: TokenType; covStatus: CovStatus; line?: number; prooftext?: string; isTop?: boolean; methodType?: string }[], provedByLines?: Record<number, number[]>): ProofGraph {
  const graph = new ProofGraph();
  const nodesByLine = new Map<number, ProofNode>();
  for (const s of specs) {
    const line = s.line ?? 1;
    const prooftext = s.prooftext || prooftextForType(s.type);
    const methodType = s.methodType ?? "correctness";
    const node = new ProofNode("test.dfy", { line, col: 0 }, { line, col: 10 }, "", methodType, prooftext);
    node.covStatus = s.covStatus;
    node.covStatusInternal = s.covStatus;
    if (!graph.hasNode(node.getId())) {
      graph.addNode(node);
    }
    if (s.isTop || s.type === TokenType.Postcondition || s.type === TokenType.LoopInvariant) {
      node.addRole("isTop");
      graph.addTopNode(node);
    }
    nodesByLine.set(line, node);
  }
  // Wire up provedBy edges
  if (provedByLines) {
    for (const [topLine, proverLines] of Object.entries(provedByLines)) {
      const topNode = nodesByLine.get(Number(topLine));
      if (!topNode) continue;
      for (const pLine of proverLines) {
        const prover = nodesByLine.get(pLine);
        if (prover) topNode.provedBy.add(prover);
      }
    }
  }
  return graph;
}

describe("classifyPostcondition", () => {
  it("none when no postconditions", () => {
    const graph = buildGraph([{ type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 1 }]);
    expect(classifyPostcondition(graph)).toBe("none");
  });
  it("strong when post has all provedBy covered", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
    ], { 1: [2] });
    expect(classifyPostcondition(graph)).toBe("strong");
  });
  it("weak when a provedBy node is uncovered", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.Uncovered, line: 2 },
    ], { 1: [2] });
    expect(classifyPostcondition(graph)).toBe("weak");
  });
  it("weak when post has no provedBy (tautology)", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.Uncovered, line: 1, prooftext: "this postcondition holds", isTop: true },
    ]);
    expect(classifyPostcondition(graph)).toBe("weak");
  });
  it("strong when only well-formedness postconditions exist", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.Uncovered, line: 1, prooftext: "this postcondition holds", isTop: true, methodType: "well-formedness" },
    ]);
    expect(classifyPostcondition(graph)).toBe("strong");
  });
  it("strong with CovTest provedBy nodes", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovTest, line: 2 },
    ], { 1: [2] });
    expect(classifyPostcondition(graph)).toBe("strong");
  });
  it("strong when non-CodeLine dep is uncovered (ignored)", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
      { type: TokenType.AssertionManual, covStatus: CovStatus.Uncovered, line: 3, prooftext: "assertion always holds" },
    ], { 1: [2, 3] });
    expect(classifyPostcondition(graph)).toBe("strong");
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
    const graph = buildGraph([]);
    expect(classifyInvariant(graph)).toBe("none");
  });
  it("strong when all provedBy nodes covered", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.CovComplete, line: 1, prooftext: "loop invariant always holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
    ], { 1: [2] });
    expect(classifyInvariant(graph)).toBe("strong");
  });
  it("weak when a provedBy node is uncovered", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.CovComplete, line: 1, prooftext: "loop invariant always holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.Uncovered, line: 2 },
    ], { 1: [2] });
    expect(classifyInvariant(graph)).toBe("weak");
  });
  it("weak when invariant has no provedBy (tautology)", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.Uncovered, line: 1, prooftext: "loop invariant always holds", isTop: true },
    ]);
    expect(classifyInvariant(graph)).toBe("weak");
  });
  it("strong when only well-formedness invariants exist", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.Uncovered, line: 1, prooftext: "loop invariant always holds", isTop: true, methodType: "well-formedness" },
    ]);
    expect(classifyInvariant(graph)).toBe("strong");
  });
});

describe("classifySpec (overall)", () => {
  it("strong when postcondition strong", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
    ], { 1: [2] });
    expect(classifySpec(graph)).toBe("strong");
  });
  it("weak when no postconditions", () => {
    const graph = buildGraph([]);
    expect(classifySpec(graph)).toBe("weak");
  });
});
