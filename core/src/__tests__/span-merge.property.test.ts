import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { getMessageClass, messagesMatch } from "../proof.js";

/**
 * Property 6: Message-class matching correctness
 * Validates: Requirements 3.1–3.5
 *
 * For any pair of messages (topMsg, rangeMsg), messagesMatch returns true iff:
 * - postcondition class: top="this postcondition holds", range="ensures clause"
 * - precondition class: top="the precondition always holds", range starts with "requires clause at"
 * - loop-invariant class: top="this loop invariant holds on entry"|"...maintained...", range="loop invariant always holds"
 * - exact class: topMsg.trim() === rangeMsg.trim()
 */

const KNOWN_TOP_MESSAGES = [
  "this postcondition holds",
  "the precondition always holds",
  "this loop invariant holds on entry",
  "this loop invariant is maintained by the loop",
] as const;

describe("Property 6: Message-class matching correctness", () => {
  describe("getMessageClass returns correct class for known messages", () => {
    it("postcondition class", () => {
      expect(getMessageClass("this postcondition holds")).toBe("postcondition");
    });

    it("precondition class", () => {
      expect(getMessageClass("the precondition always holds")).toBe("precondition");
    });

    it("loop-invariant class (holds on entry)", () => {
      expect(getMessageClass("this loop invariant holds on entry")).toBe("loop-invariant");
    });

    it("loop-invariant class (maintained by the loop)", () => {
      expect(getMessageClass("this loop invariant is maintained by the loop")).toBe("loop-invariant");
    });

    it("random strings return exact class", () => {
      fc.assert(
        fc.property(fc.string(), (msg) => {
          const cls = getMessageClass(msg);
          if (KNOWN_TOP_MESSAGES.includes(msg as any)) {
            // Known messages get their specific class
            expect(["postcondition", "precondition", "loop-invariant"]).toContain(cls);
          } else {
            expect(cls).toBe("exact");
          }
        }),
        { numRuns: 100 },
      );
    });
  });

  describe("messagesMatch correctly pairs messages by class", () => {
    it("postcondition: top matches 'ensures clause' only", () => {
      expect(messagesMatch("this postcondition holds", "ensures clause")).toBe(true);
      expect(messagesMatch("this postcondition holds", "something else")).toBe(false);
      expect(messagesMatch("this postcondition holds", "requires clause at foo")).toBe(false);
    });

    it("precondition: top matches any rangeMsg starting with 'requires clause at'", () => {
      fc.assert(
        fc.property(fc.string(), (suffix) => {
          const rangeMsg = "requires clause at" + suffix;
          expect(messagesMatch("the precondition always holds", rangeMsg)).toBe(true);
        }),
        { numRuns: 100 },
      );
      expect(messagesMatch("the precondition always holds", "ensures clause")).toBe(false);
      expect(messagesMatch("the precondition always holds", "something else")).toBe(false);
    });

    it("loop-invariant: both top variants match 'loop invariant always holds'", () => {
      expect(messagesMatch("this loop invariant holds on entry", "loop invariant always holds")).toBe(true);
      expect(messagesMatch("this loop invariant is maintained by the loop", "loop invariant always holds")).toBe(true);
      expect(messagesMatch("this loop invariant holds on entry", "something else")).toBe(false);
      expect(messagesMatch("this loop invariant is maintained by the loop", "ensures clause")).toBe(false);
    });

    it("exact class: matches iff trimmed strings are equal", () => {
      fc.assert(
        fc.property(fc.string(), fc.string(), (a, b) => {
          // Skip known top messages to isolate exact class
          if (KNOWN_TOP_MESSAGES.includes(a as any)) return;

          const result = messagesMatch(a, b);
          const expected = a.trim() === b.trim();
          expect(result).toBe(expected);
        }),
        { numRuns: 100 },
      );
    });

    it("cross-class: if getMessageClass(top) !== getMessageClass(range-source) for non-exact, messagesMatch is false", () => {
      // Generate random pairs and verify cross-class mismatch
      fc.assert(
        fc.property(fc.string(), (rangeMsg) => {
          // postcondition top should not match non-"ensures clause" range
          if (rangeMsg !== "ensures clause") {
            expect(messagesMatch("this postcondition holds", rangeMsg)).toBe(false);
          }
        }),
        { numRuns: 100 },
      );
    });
  });

  describe("messagesMatch is false for cross-class pairs", () => {
    // Generators for each class's range messages
    const postconditionRange = fc.constant("ensures clause");
    const preconditionRange = fc.string().map((s) => "requires clause at" + s);
    const loopInvariantRange = fc.constant("loop invariant always holds");

    // Top messages per class
    const postconditionTop = fc.constant("this postcondition holds");
    const preconditionTop = fc.constant("the precondition always holds");
    const loopInvariantTops = fc.oneof(
      fc.constant("this loop invariant holds on entry"),
      fc.constant("this loop invariant is maintained by the loop"),
    );

    it("postcondition top does not match precondition or loop-invariant ranges", () => {
      fc.assert(
        fc.property(preconditionRange, (range) => {
          expect(messagesMatch("this postcondition holds", range)).toBe(false);
        }),
        { numRuns: 100 },
      );
      fc.assert(
        fc.property(loopInvariantRange, (range) => {
          expect(messagesMatch("this postcondition holds", range)).toBe(false);
        }),
        { numRuns: 100 },
      );
    });

    it("precondition top does not match postcondition or loop-invariant ranges", () => {
      fc.assert(
        fc.property(postconditionRange, (range) => {
          expect(messagesMatch("the precondition always holds", range)).toBe(false);
        }),
        { numRuns: 100 },
      );
      fc.assert(
        fc.property(loopInvariantRange, (range) => {
          expect(messagesMatch("the precondition always holds", range)).toBe(false);
        }),
        { numRuns: 100 },
      );
    });

    it("loop-invariant top does not match postcondition or precondition ranges", () => {
      fc.assert(
        fc.property(loopInvariantTops, postconditionRange, (top, range) => {
          expect(messagesMatch(top, range)).toBe(false);
        }),
        { numRuns: 100 },
      );
      fc.assert(
        fc.property(loopInvariantTops, preconditionRange, (top, range) => {
          expect(messagesMatch(top, range)).toBe(false);
        }),
        { numRuns: 100 },
      );
    });

    it("exact class top does not match other class ranges (unless string-equal after trim)", () => {
      // Generate a top message that's NOT one of the known messages
      const exactTop = fc.string().filter((s) => !KNOWN_TOP_MESSAGES.includes(s as any));

      fc.assert(
        fc.property(exactTop, postconditionRange, (top, range) => {
          // Only matches if top.trim() === range.trim()
          const expected = top.trim() === range.trim();
          expect(messagesMatch(top, range)).toBe(expected);
        }),
        { numRuns: 100 },
      );

      fc.assert(
        fc.property(exactTop, loopInvariantRange, (top, range) => {
          const expected = top.trim() === range.trim();
          expect(messagesMatch(top, range)).toBe(expected);
        }),
        { numRuns: 100 },
      );
    });
  });
});
