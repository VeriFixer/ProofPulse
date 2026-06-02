import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { classifyNodeType } from "../proof-node.js";
import { TokenType } from "../types.js";

/**
 * Property 3: TokenType assignment matches heuristic
 */

const postconditionPatterns = [
  "this postcondition holds",
  "ensures clause",
] as const;

const preconditionPatterns = ["precondition always holds"] as const;

const assertionManualPatterns = ["assertion always holds"] as const;

const assertionAutomaticPatterns = [
  "index in range",
  "target object is never null",
  "which is subject to definite-assignment rules, is always initialized at this return point",
  "which is subject to definite-assignment rules, is always initialized here",
] as const;

const allKeywordPatterns = [
  ...postconditionPatterns,
  ...preconditionPatterns,
  ...assertionManualPatterns,
  ...assertionAutomaticPatterns,
];

function expectedTokenType(
  prooftext: string,
  isTopAssertion: boolean,
): TokenType {
  if (prooftext.includes("this postcondition holds")) {
    return TokenType.Postcondition;
  }
  if (prooftext.includes("ensures clause")) {
    return TokenType.Postcondition;
  }
  if (prooftext.includes("precondition always holds")) {
    return TokenType.Precondition;
  }
  if (prooftext.includes("assertion always holds")) {
    return TokenType.AssertionManual;
  }
  if (
    prooftext.includes("index in range") ||
    prooftext.includes("target object is never null") ||
    prooftext.includes(
      "which is subject to definite-assignment rules, is always initialized at this return point",
    ) ||
    prooftext.includes(
      "which is subject to definite-assignment rules, is always initialized here",
    )
  ) {
    return TokenType.AssertionAutomatic;
  }
  if (isTopAssertion) {
    return TokenType.AssertionAutomatic;
  }
  return TokenType.CodeLine;
}

const prooftextWithKeyword = fc
  .record({
    keyword: fc.constantFrom(...allKeywordPatterns),
    prefix: fc.string({ maxLength: 20 }),
    suffix: fc.string({ maxLength: 20 }),
  })
  .map(({ keyword, prefix, suffix }) => `${prefix}${keyword}${suffix}`);

const prooftextWithoutKeyword = fc
  .string({ minLength: 0, maxLength: 50 })
  .filter((s) => !allKeywordPatterns.some((kw) => s.includes(kw)));

describe("Property 3: TokenType assignment matches heuristic", () => {
  it("assigns correct TokenType for prooftext with known keywords", () => {
    fc.assert(
      fc.property(
        prooftextWithKeyword,
        fc.boolean(),
        (prooftext, isTopAssertion) => {
          expect(classifyNodeType([prooftext], isTopAssertion)).toBe(expectedTokenType(prooftext, isTopAssertion));
        },
      ),
      { numRuns: 200 },
    );
  });

  it("assigns correct TokenType for prooftext without keywords", () => {
    fc.assert(
      fc.property(
        prooftextWithoutKeyword,
        fc.boolean(),
        (prooftext, isTopAssertion) => {
          expect(classifyNodeType([prooftext], isTopAssertion)).toBe(expectedTokenType(prooftext, isTopAssertion));
        },
      ),
      { numRuns: 200 },
    );
  });

  it("classifyNodeType is consistent across calls", () => {
    fc.assert(
      fc.property(
        fc.oneof(prooftextWithKeyword, prooftextWithoutKeyword),
        fc.boolean(),
        (prooftext, isTopAssertion) => {
          expect(classifyNodeType([prooftext], isTopAssertion)).toBe(classifyNodeType([prooftext], isTopAssertion));
        },
      ),
      { numRuns: 200 },
    );
  });
});
