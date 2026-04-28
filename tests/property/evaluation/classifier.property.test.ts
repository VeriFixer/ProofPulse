import { describe, it, expect } from "vitest";
import fc from "fast-check";
import { classifyPostcondition, classifyPrecondition, classifyInvariant } from "../../../evaluation/src/classifier.js";
import { TokenType, CovStatus, type NodeData, type SourceLocation } from "@proofpulse/core";

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

function isInv(n: NodeData) { return n.prooftext.includes("loop invariant"); }

describe("Property 2: Classification correctness", () => {
  it("classifyPostcondition matches definition", () => {
    fc.assert(fc.property(
      fc.array(arbNodeData, { minLength: 0, maxLength: 20 }),
      (nodes) => {
        const posts = nodes.filter((n) => n.type === TokenType.Postcondition);
        const body = nodes.filter((n) => n.type === TokenType.CodeLine && !isInv(n));
        const result = classifyPostcondition(nodes);

        if (posts.length === 0) { expect(result).toBe("none"); return; }
        const allPostCov = posts.every((n) => n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest);
        const allBodyCov = body.every((n) => n.covStatus === CovStatus.CovComplete);
        expect(result).toBe(allPostCov && allBodyCov ? "strong" : "weak");
      }
    ), { numRuns: 100 });
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

  it("classifyInvariant matches definition", () => {
    fc.assert(fc.property(
      fc.array(arbNodeData, { minLength: 0, maxLength: 20 }),
      (nodes) => {
        const invs = nodes.filter((n) => isInv(n));
        const result = classifyInvariant(nodes);
        if (invs.length === 0) { expect(result).toBe("none"); return; }
        const allCov = invs.every((n) => n.covStatus === CovStatus.CovComplete || n.covStatus === CovStatus.CovTest);
        expect(result).toBe(allCov ? "strong" : "weak");
      }
    ), { numRuns: 100 });
  });
});
