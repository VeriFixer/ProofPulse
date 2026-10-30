import { describe, it, expect } from "vitest";
import { classifyPostcondition, classifyPrecondition, classifyInvariant, classifySpec, classifyMethods } from "../classifier.js";
import { TokenType, CovStatus, UnitKind, type NodeData, ProofNode, ProofGraph, nodeKindForTokenType } from "@proofpulse/core";
import { Classification, PreconditionNeed, SpecStrength } from "../types.js";

function makeNode(type: TokenType, covStatus: CovStatus, line = 1, prooftext = "", methodType?: UnitKind): NodeData {
  return {
    id: `node-${line}`, file: "test.dfy",
    start: { line, col: 0 }, end: { line, col: 10 },
    prooftexts: [prooftext], roles: { isTop: false, isCall: false, isProvedBy: false, isUnused: false }, type, covStatus, covStatusInternal: covStatus,
    ...(methodType ? { methodType } : {}),
  };
}

/** A representative Dafny message for each TokenType (the node kind is passed explicitly). */
function prooftextForType(type: TokenType): string {
  switch (type) {
    case TokenType.Postcondition: return "this postcondition holds";
    case TokenType.Precondition: return "precondition always holds";
    case TokenType.LoopInvariant: return "loop invariant always holds";
    case TokenType.Call: return "ensures clause at foo(1,1)-(1,5)";
    case TokenType.AssertionManual: return "assertion always holds";
    case TokenType.AssertionAutomatic: return "index in range";
    case TokenType.Condition: return "condition atom";
    default: return "some code line";
  }
}

/** Build a ProofGraph from specs. Postcondition/LoopInvariant types are added as tops.
 * Each node's kind is derived from its TokenType via nodeKindForTokenType.
 * provedByLines maps a top's line to an array of prover lines (for building edges). */
function buildGraph(specs: { type: TokenType; covStatus: CovStatus; line?: number; prooftext?: string; isTop?: boolean; methodType?: UnitKind; method?: string }[], provedByLines?: Record<number, number[]>): ProofGraph {
  const graph = new ProofGraph();
  const nodesByLine = new Map<number, ProofNode>();
  for (const s of specs) {
    const line = s.line ?? 1;
    const prooftext = s.prooftext || prooftextForType(s.type);
    const methodType = s.methodType ?? UnitKind.Correctness;
    const node = new ProofNode("test.dfy", { line, col: 0 }, { line, col: 10 }, s.method ?? "", methodType, prooftext, nodeKindForTokenType(s.type));
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
    expect(classifyPostcondition(graph)).toBe(SpecStrength.None);
  });
  it("strong when post has all provedBy covered", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
    ], { 1: [2] });
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Strong);
  });
  it("weak when a provedBy node is uncovered", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.Uncovered, line: 2 },
    ], { 1: [2] });
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Weak);
  });
  it("weak when post has no provedBy (tautology)", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.Uncovered, line: 1, prooftext: "this postcondition holds", isTop: true },
    ]);
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Weak);
  });
  it("strong when only well-formedness postconditions exist", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.Uncovered, line: 1, prooftext: "this postcondition holds", isTop: true, methodType: UnitKind.WellFormedness },
    ]);
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Strong);
  });
  // CovTest (covered only by test/ghost code) counts as weak since ee280f2.
  it("weak with CovTest provedBy nodes", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovTest, line: 2 },
    ], { 1: [2] });
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Weak);
  });
  it("weak when only non-CodeLine deps exist", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.AssertionManual, covStatus: CovStatus.CovComplete, line: 2, prooftext: "assertion always holds" },
    ], { 1: [2] });
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Weak);
  });
  it("well-formedness tops are ignored when correctness tops exist", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
      { type: TokenType.Postcondition, covStatus: CovStatus.Uncovered, line: 3, isTop: true, methodType: UnitKind.WellFormedness },
    ], { 1: [2] });
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Strong);
  });
  it("strong when non-CodeLine dep is uncovered (ignored)", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
      { type: TokenType.AssertionManual, covStatus: CovStatus.Uncovered, line: 3, prooftext: "assertion always holds" },
    ], { 1: [2, 3] });
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Strong);
  });
});

describe("classifyPrecondition", () => {
  it("none when no preconditions", () => {
    expect(classifyPrecondition([])).toBe(PreconditionNeed.None);
  });
  it("required when all covered", () => {
    expect(classifyPrecondition([
      makeNode(TokenType.Precondition, CovStatus.CovComplete, 1),
    ])).toBe(PreconditionNeed.Required);
  });
  // Optional only when ALL correctness preconditions are uncovered (since 0285ad8).
  it("required when only some are uncovered", () => {
    expect(classifyPrecondition([
      makeNode(TokenType.Precondition, CovStatus.CovComplete, 1),
      makeNode(TokenType.Precondition, CovStatus.Uncovered, 2),
    ])).toBe(PreconditionNeed.Required);
  });
  it("ignores well-formedness preconditions", () => {
    expect(classifyPrecondition([
      makeNode(TokenType.Precondition, CovStatus.CovComplete, 1, "", UnitKind.WellFormedness),
      makeNode(TokenType.Precondition, CovStatus.Uncovered, 2, "", UnitKind.Correctness),
    ])).toBe(PreconditionNeed.Optional);
    expect(classifyPrecondition([
      makeNode(TokenType.Precondition, CovStatus.CovComplete, 1, "", UnitKind.WellFormedness),
    ])).toBe(PreconditionNeed.None);
  });
  it("optional when all uncovered", () => {
    expect(classifyPrecondition([
      makeNode(TokenType.Precondition, CovStatus.Uncovered, 1),
    ])).toBe(PreconditionNeed.Optional);
  });
});

describe("classifyInvariant", () => {
  it("none when no invariants", () => {
    const graph = buildGraph([]);
    expect(classifyInvariant(graph)).toBe(SpecStrength.None);
  });
  it("strong when all provedBy nodes covered", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.CovComplete, line: 1, prooftext: "loop invariant always holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
    ], { 1: [2] });
    expect(classifyInvariant(graph)).toBe(SpecStrength.Strong);
  });
  it("weak when a provedBy node is uncovered", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.CovComplete, line: 1, prooftext: "loop invariant always holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.Uncovered, line: 2 },
    ], { 1: [2] });
    expect(classifyInvariant(graph)).toBe(SpecStrength.Weak);
  });
  it("weak when invariant has no provedBy (tautology)", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.Uncovered, line: 1, prooftext: "loop invariant always holds", isTop: true },
    ]);
    expect(classifyInvariant(graph)).toBe(SpecStrength.Weak);
  });
  it("strong when only well-formedness invariants exist", () => {
    const graph = buildGraph([
      { type: TokenType.LoopInvariant, covStatus: CovStatus.Uncovered, line: 1, prooftext: "loop invariant always holds", isTop: true, methodType: UnitKind.WellFormedness },
    ]);
    expect(classifyInvariant(graph)).toBe(SpecStrength.Strong);
  });
});

describe("classifySpec (overall)", () => {
  it("strong when postcondition strong", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, prooftext: "this postcondition holds", isTop: true },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
    ], { 1: [2] });
    expect(classifySpec(graph)).toBe(Classification.Strong);
  });
  it("weak when no postconditions", () => {
    const graph = buildGraph([]);
    expect(classifySpec(graph)).toBe(Classification.Weak);
  });
});

describe("condition atoms", () => {
  it("an unused condition atom makes the postcondition weak", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1 },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
      { type: TokenType.Condition, covStatus: CovStatus.Uncovered, line: 3 },
    ], { 1: [2, 3] });
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Weak);
  });

  it("used condition atoms keep the postcondition strong", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1 },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2 },
      { type: TokenType.Condition, covStatus: CovStatus.CovComplete, line: 3 },
    ], { 1: [2, 3] });
    expect(classifyPostcondition(graph)).toBe(SpecStrength.Strong);
  });
});

describe("classifyMethods", () => {
  it("classifies each method on its own", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, method: "Good" },
      { type: TokenType.CodeLine, covStatus: CovStatus.CovComplete, line: 2, method: "Good" },
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 3, method: "M.C.Bad" },
      { type: TokenType.CodeLine, covStatus: CovStatus.Uncovered, line: 4, method: "M.C.Bad" },
    ], { 1: [2], 3: [4] });
    expect(classifySpec(graph)).toBe(Classification.Weak);
    const methods = classifyMethods(graph, graph.getAllNodes());
    expect(methods.map(m => [m.method, m.classification, m.categories.postcondition])).toEqual([
      ["Good", Classification.Strong, SpecStrength.Strong],
      ["M.C.Bad", Classification.Weak, SpecStrength.Weak],
    ]);
  });

  it("skips well-formedness-only methods", () => {
    const graph = buildGraph([
      { type: TokenType.Postcondition, covStatus: CovStatus.CovComplete, line: 1, method: "F", methodType: UnitKind.WellFormedness },
    ]);
    expect(classifyMethods(graph, graph.getAllNodes())).toEqual([]);
  });
});
