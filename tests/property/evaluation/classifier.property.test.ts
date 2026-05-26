import { describe, it, expect } from "vitest";
import fc from "fast-check";
import { classifyPostcondition, classifyPrecondition, classifyInvariant } from "../../../evaluation/src/classifier.js";
import { TokenType, CovStatus, type NodeData, type SourceLocation, Node, ProofGraph } from "@proofpulse/core";

const allTokenTypes = Object.values(TokenType);
const allCovStatuses = Object.values(CovStatus);

const arbTokenType = fc.constantFrom(...allTokenTypes);
const arbCovStatus = fc.constantFrom(...allCovStatuses);
const arbSourceLocation: fc.Arbitrary<SourceLocation> = fc.record({ line: fc.nat({ max: 1000 }), col: fc.nat({ max: 200 }) });

const arbNodeData: fc.Arbitrary<NodeData> = fc.record({
  id: fc.string({ minLength: 1, maxLength: 10 }),
  file: fc.constant("test.dfy"),
  start: arbSourceLocation, end: arbSourceLocation,
  prooftext: fc.constantFrom("", "loop invariant always holds", "this postcondition holds"),
  isTopAssertion: fc.boolean(),
  type: arbTokenType,
  covStatus: arbCovStatus,
  covStatusInternal: arbCovStatus,
});

function isInv(n: { prooftext: string }) { return n.prooftext.includes("loop invariant"); }

/** Build a ProofGraph from NodeData-like specs for property testing. */
function buildGraphFromSpecs(specs: { type: TokenType; covStatus: CovStatus; line: number; col?: number; prooftext: string; isTop: boolean }[]): ProofGraph {
  const graph = new ProofGraph();
  for (const s of specs) {
    const col = s.col ?? 0;
    const node = new Node("test.dfy", s.line, col, s.line, col + 10, s.prooftext, s.isTop);
    node.type = s.type;
    node.covStatus = s.covStatus;
    node.covStatusInternal = s.covStatus;
    if (!graph.hasNode(node.id)) {
      graph.addNode(node);
      if (s.isTop) {
        graph.addTopNode(node);
      }
    }
  }
  return graph;
}

/** Arbitrary for graph node specs — generates unique line positions. */
const arbGraphNodeSpec = fc.record({
  type: arbTokenType,
  covStatus: arbCovStatus,
  prooftext: fc.constantFrom("", "loop invariant always holds", "this postcondition holds"),
});

function makeGraphSpecs(nodes: { type: TokenType; covStatus: CovStatus; prooftext: string }[]) {
  return nodes.map((n, i) => ({
    ...n,
    line: i + 1,
    col: 0,
    isTop: n.type === TokenType.Postcondition || n.type === TokenType.LoopInvariant,
  }));
}

describe("Property 2: Classification correctness", () => {
  it("classifyPostcondition: none when no postcondition tops", () => {
    fc.assert(fc.property(
      fc.array(arbGraphNodeSpec, { minLength: 0, maxLength: 20 }),
      (nodes) => {
        const specs = makeGraphSpecs(nodes.filter(n => n.type !== TokenType.Postcondition));
        const graph = buildGraphFromSpecs(specs);
        expect(classifyPostcondition(graph)).toBe("none");
      }
    ), { numRuns: 50 });
  });

  it("classifyPostcondition: weak when any postcondition top uncovered", () => {
    fc.assert(fc.property(
      fc.array(arbGraphNodeSpec, { minLength: 1, maxLength: 20 }),
      (extraNodes) => {
        // Force at least one uncovered postcondition top
        const specs = makeGraphSpecs([
          { type: TokenType.Postcondition, covStatus: CovStatus.Uncovered, prooftext: "this postcondition holds" },
          ...extraNodes,
        ]);
        const graph = buildGraphFromSpecs(specs);
        const result = classifyPostcondition(graph);
        expect(result).toBe("weak");
      }
    ), { numRuns: 50 });
  });

  it("classifyPostcondition: strong when all post tops covered and no uncovered CodeLine fallback", () => {
    fc.assert(fc.property(
      fc.array(fc.constantFrom(CovStatus.CovComplete, CovStatus.CovTest), { minLength: 1, maxLength: 5 }),
      fc.array(fc.constantFrom(CovStatus.CovComplete, CovStatus.CovTest), { minLength: 0, maxLength: 5 }),
      (postStatuses, bodyStatuses) => {
        const specs = makeGraphSpecs([
          ...postStatuses.map(s => ({ type: TokenType.Postcondition, covStatus: s, prooftext: "this postcondition holds" })),
          ...bodyStatuses.map(s => ({ type: TokenType.CodeLine, covStatus: s, prooftext: "" })),
        ]);
        const graph = buildGraphFromSpecs(specs);
        // No scope set → fallback to CodeLine nodes → all covered → strong
        expect(classifyPostcondition(graph)).toBe("strong");
      }
    ), { numRuns: 50 });
  });

  it("classifyPrecondition matches definition", () => {
    fc.assert(fc.property(
      fc.array(arbNodeData, { minLength: 0, maxLength: 20 }),
      (nodes) => {
        const pres = nodes.filter((n) => n.type === TokenType.Precondition);
        const result = classifyPrecondition(nodes);
        if (pres.length === 0) { expect(result).toBe("none"); return; }
        const anyUncov = pres.some((n) => n.covStatus === CovStatus.Uncovered);
        expect(result).toBe(anyUncov ? "optional" : "required");
      }
    ), { numRuns: 100 });
  });

  it("classifyInvariant: none when no invariant tops", () => {
    fc.assert(fc.property(
      fc.array(arbGraphNodeSpec, { minLength: 0, maxLength: 20 }),
      (nodes) => {
        const specs = makeGraphSpecs(nodes.filter(n => n.type !== TokenType.LoopInvariant));
        const graph = buildGraphFromSpecs(specs);
        expect(classifyInvariant(graph)).toBe("none");
      }
    ), { numRuns: 50 });
  });

  it("classifyInvariant: strong when scope/fallback all covered", () => {
    fc.assert(fc.property(
      fc.array(fc.constantFrom(CovStatus.CovComplete, CovStatus.CovTest), { minLength: 1, maxLength: 5 }),
      fc.array(fc.constantFrom(CovStatus.CovComplete, CovStatus.CovTest), { minLength: 0, maxLength: 5 }),
      (invStatuses, bodyStatuses) => {
        const specs = makeGraphSpecs([
          ...invStatuses.map(s => ({ type: TokenType.LoopInvariant, covStatus: s, prooftext: "loop invariant always holds" })),
          ...bodyStatuses.map(s => ({ type: TokenType.CodeLine, covStatus: s, prooftext: "" })),
        ]);
        const graph = buildGraphFromSpecs(specs);
        expect(classifyInvariant(graph)).toBe("strong");
      }
    ), { numRuns: 50 });
  });

  it("classifyInvariant: weak when invariant top uncovered", () => {
    fc.assert(fc.property(
      fc.array(arbGraphNodeSpec, { minLength: 0, maxLength: 5 }),
      (extraNodes) => {
        const specs = makeGraphSpecs([
          { type: TokenType.LoopInvariant, covStatus: CovStatus.Uncovered, prooftext: "loop invariant always holds" },
          ...extraNodes,
        ]);
        const graph = buildGraphFromSpecs(specs);
        expect(classifyInvariant(graph)).toBe("weak");
      }
    ), { numRuns: 50 });
  });
});
