import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { Node } from "../node.js";
import { TokenType } from "../types.js";

/**
 * Property 3: TokenType assignment matches heuristic
 * Validates: Requirements 3.2
 *
 * For any Node with a given prooftext string, the assigned TokenType SHALL match
 * the heuristic rules defined in updateIsTopAssertion.
 */

const postconditionPatterns = [
  "this postcondition holds",
  "ensures clause",
] as const;

const preconditionPatterns = ["method requires clause"] as const;

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
  if (
    prooftext.includes("this postcondition holds") ||
    prooftext.includes("ensures clause")
  ) {
    return TokenType.Postcondition;
  }
  if (prooftext.includes("method requires clause")) {
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

/** Generator: prooftext containing a known keyword with random surrounding text */
const prooftextWithKeyword = fc
  .record({
    keyword: fc.constantFrom(...allKeywordPatterns),
    prefix: fc.string({ maxLength: 20 }),
    suffix: fc.string({ maxLength: 20 }),
  })
  .map(({ keyword, prefix, suffix }) => `${prefix}${keyword}${suffix}`);

/** Generator: prooftext guaranteed to contain NO known keywords */
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
          const node = new Node("test.dfy", 1, 0, 1, 10, prooftext, isTopAssertion);
          expect(node.type).toBe(expectedTokenType(prooftext, isTopAssertion));
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
          const node = new Node("test.dfy", 1, 0, 1, 10, prooftext, isTopAssertion);
          expect(node.type).toBe(expectedTokenType(prooftext, isTopAssertion));
        },
      ),
      { numRuns: 200 },
    );
  });

  it("assigns correct TokenType for fully random prooftext and isTopAssertion", () => {
    fc.assert(
      fc.property(
        fc.oneof(prooftextWithKeyword, prooftextWithoutKeyword),
        fc.boolean(),
        (prooftext, isTopAssertion) => {
          const node = new Node("test.dfy", 1, 0, 1, 10, prooftext, isTopAssertion);
          expect(node.type).toBe(expectedTokenType(prooftext, isTopAssertion));
        },
      ),
      { numRuns: 200 },
    );
  });
});
