import { describe, it, expect } from "vitest";
import { classifyPostcondition, classifyPrecondition, classifyInvariant, classifySpec } from "../../../evaluation/src/classifier.js";
import { TokenType, CovStatus, type NodeData, Node, ProofGraph } from "@proofpulse/core";

function makeNode(type: TokenType, covStatus: CovStatus, line = 1, prooftext = ""): NodeData {
  return {
    id: `node-${line}`, file: "test.dfy",
    start: { line, col: 0 }, end: { line, col: 10 },
    prooftext, isTopAssertion: false, type, covStatus, covStatusInternal: covStatus,
  };
}

/** Build a ProofGraph from NodeData specs. Nodes with isTopAssertion or Postcondition/LoopInvariant type are added as tops. */
function buildGraph(specs: { type: TokenType; covStatus: CovStatus; line?: number; prooftext?: string; isTop?: boolean }[]): ProofGraph {
  const graph = new ProofGraph();
  for (const s of specs) {
    const line = s.line ?? 1;
    const prooftext = s.prooftext ?? "";
    const node = new Node("test.dfy", line, 0, line, 10, prooftext, s.isTop ?? false);
    // Override type and covStatus
    node.type = s.type;
    node.covStatus = s.covStatus;
    node.covStatusInternal = s.covStatus;
    if (!graph.hasNode(node.id)) {
      graph.addNode(node);
    }
    if (s.isTop || s.type === TokenType.Postcondition || s.type === TokenType.LoopInvariant) {
      node.isTopAssertion = true;
      if (!graph.hasTopNode(node.id)) {
        graph.addTopNode(node);
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
  it("strong when post covered and body complete", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
    ]);
    expect(classifyPostcondition(graph)).toBe("strong");
  });
  it("weak when post uncovered", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.Uncovered, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
    ]);
    expect(classifyPostcondition(graph)).toBe("weak");
  });
  it("strong when post covered and no scope (tops sufficient)", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.Precondition, covStatus: CovStatus.Uncovered, line: 2, prooftext: "precondition always holds" },
    ]);
    // No scope → tops covered → strong (precondition irrelevant)
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
  it("strong when all invariant tops covered (no scope)", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.CovComplete, line: 1, prooftext: "loop invariant always holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.Uncovered, line: 2 },
    ]);
    // No scope data → classification based on tops only → strong
    expect(classifyInvariant(graph)).toBe("strong");
  });
  it("weak when invariant top uncovered", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.Uncovered, line: 1, prooftext: "loop invariant always holds", isTop: true },
    ]);
    expect(classifyInvariant(graph)).toBe("weak");
  });
});

describe("classifySpec (overall)", () => {
  it("strong when postcondition strong", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
    ]);
    expect(classifySpec(graph)).toBe("strong");
  });
  it("weak when no postconditions", () => {
    const graph = buildGraph([]);
    expect(classifySpec(graph)).toBe("weak");
  });
});
