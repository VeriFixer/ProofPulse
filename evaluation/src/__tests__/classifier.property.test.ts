import { describe, it, expect } from "vitest";
import fc from "fast-check";
import { classifySpec } from "../classifier.js";
import {
  TokenType,
  CovStatus,
  type NodeData,
  type SourceLocation,
} from "@proofpulse/core";

/**
 * Feature: dafny-synthesis-benchmark, Property 2: Classification correctness
 * Validates: Requirements 3.2, 3.3, 3.5
 */

const allTokenTypes = [
  TokenType.Undefined,
  TokenType.Precondition,
  TokenType.Postcondition,
  TokenType.AssertionManual,
  TokenType.AssertionAutomatic,
  TokenType.CodeLine,
] as const;

const allCovStatuses = [
  CovStatus.CovComplete,
  CovStatus.CovTest,
  CovStatus.Uncovered,
] as const;

const arbTokenType = fc.constantFrom(...allTokenTypes);
const arbCovStatus = fc.constantFrom(...allCovStatuses);

const arbSourceLocation: fc.Arbitrary<SourceLocation> = fc.record({
  line: fc.nat({ max: 1000 }),
  col: fc.nat({ max: 200 }),
});

const arbNodeData: fc.Arbitrary<NodeData> = fc.record({
  id: fc.string({ minLength: 1, maxLength: 10 }),
  file: fc.string({ minLength: 1, maxLength: 20 }),
  start: arbSourceLocation,
  end: arbSourceLocation,
  prooftext: fc.string({ maxLength: 50 }),
  isTopAssertion: fc.boolean(),
  type: arbTokenType,
  covStatus: arbCovStatus,
  covStatusInternal: arbCovStatus,
});

function expectedClassification(nodes: NodeData[]): "strong" | "weak" {
  const postconditions = nodes.filter(
    (n) => n.type === TokenType.Postcondition
  );
  const bodyNodes = nodes.filter((n) => n.type === TokenType.CodeLine);

  if (postconditions.length === 0) return "weak";

  const allPostCovered = postconditions.every(
    (n) =>
      n.covStatus === CovStatus.CovComplete ||
      n.covStatus === CovStatus.CovTest
  );
  if (!allPostCovered) return "weak";

  const allBodyComplete = bodyNodes.every(
    (n) => n.covStatus === CovStatus.CovComplete
  );
  if (!allBodyComplete) return "weak";

  return "strong";
}

describe("Property 2: Classification correctness", () => {
  it("classifySpec matches strong/weak definition for any NodeData[]", () => {
    fc.assert(
      fc.property(
        fc.array(arbNodeData, { minLength: 0, maxLength: 20 }),
        (nodes) => {
          const result = classifySpec(nodes);
          const expected = expectedClassification(nodes);
          expect(result).toBe(expected);
        }
      ),
      { numRuns: 100 }
    );
  });
});
