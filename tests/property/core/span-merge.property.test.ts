import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import { getMessageClass, messagesMatch, isContained } from "../../../core/src/proof.js";

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
  describe("getMessageClass always returns a valid class", () => {
    it("returns one of the four valid classes for any string", () => {
      fc.assert(
        fc.property(fc.string(), (msg) => {
          const cls = getMessageClass(msg);
          expect(["postcondition", "precondition", "loop-invariant", "exact"]).toContain(cls);
        }),
        { numRuns: 100 },
      );
    });
  });

  describe("getMessageClass maps known top messages to correct classes", () => {
    it("'this postcondition holds' → 'postcondition'", () => {
      expect(getMessageClass("this postcondition holds")).toBe("postcondition");
    });

    it("'the precondition always holds' → 'precondition'", () => {
      expect(getMessageClass("the precondition always holds")).toBe("precondition");
    });

    it("'this loop invariant holds on entry' → 'loop-invariant'", () => {
      expect(getMessageClass("this loop invariant holds on entry")).toBe("loop-invariant");
    });

    it("'this loop invariant is maintained by the loop' → 'loop-invariant'", () => {
      expect(getMessageClass("this loop invariant is maintained by the loop")).toBe("loop-invariant");
    });

    it("any other string → 'exact'", () => {
      fc.assert(
        fc.property(
          fc.string().filter((s) => !KNOWN_TOP_MESSAGES.includes(s as any)),
          (msg) => {
            expect(getMessageClass(msg)).toBe("exact");
          },
        ),
        { numRuns: 100 },
      );
    });
  });

  describe("messagesMatch correctness per class", () => {
    it("postcondition class: matches only 'ensures clause'", () => {
      expect(messagesMatch("this postcondition holds", "ensures clause")).toBe(true);
      fc.assert(
        fc.property(
          fc.string().filter((s) => s !== "ensures clause"),
          (range) => {
            expect(messagesMatch("this postcondition holds", range)).toBe(false);
          },
        ),
        { numRuns: 100 },
      );
    });

    it("precondition class: matches only strings starting with 'requires clause at'", () => {
      fc.assert(
        fc.property(fc.string(), (suffix) => {
          expect(messagesMatch("the precondition always holds", "requires clause at" + suffix)).toBe(true);
        }),
        { numRuns: 100 },
      );
      fc.assert(
        fc.property(
          fc.string().filter((s) => !s.startsWith("requires clause at")),
          (range) => {
            expect(messagesMatch("the precondition always holds", range)).toBe(false);
          },
        ),
        { numRuns: 100 },
      );
    });

    it("loop-invariant class: matches only 'loop invariant always holds'", () => {
      const loopTops = [
        "this loop invariant holds on entry",
        "this loop invariant is maintained by the loop",
      ];
      for (const top of loopTops) {
        expect(messagesMatch(top, "loop invariant always holds")).toBe(true);
      }
      fc.assert(
        fc.property(
          fc.constantFrom(...loopTops),
          fc.string().filter((s) => s !== "loop invariant always holds"),
          (top, range) => {
            expect(messagesMatch(top, range)).toBe(false);
          },
        ),
        { numRuns: 100 },
      );
    });

    it("exact class: matches only when topMessage.trim() === rangeMessage.trim()", () => {
      fc.assert(
        fc.property(
          fc.string().filter((s) => !KNOWN_TOP_MESSAGES.includes(s as any)),
          fc.string(),
          (top, range) => {
            const expected = top.trim() === range.trim();
            expect(messagesMatch(top, range)).toBe(expected);
          },
        ),
        { numRuns: 100 },
      );
    });
  });

  describe("messagesMatch is false for cross-class pairs", () => {
    const postconditionRange = fc.constant("ensures clause");
    const preconditionRange = fc.string().map((s) => "requires clause at" + s);
    const loopInvariantRange = fc.constant("loop invariant always holds");

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
      const loopTops = fc.constantFrom(
        "this loop invariant holds on entry",
        "this loop invariant is maintained by the loop",
      );
      fc.assert(
        fc.property(loopTops, postconditionRange, (top, range) => {
          expect(messagesMatch(top, range)).toBe(false);
        }),
        { numRuns: 100 },
      );
      fc.assert(
        fc.property(loopTops, preconditionRange, (top, range) => {
          expect(messagesMatch(top, range)).toBe(false);
        }),
        { numRuns: 100 },
      );
    });
  });
});

/**
 * Property 2: Containment predicate geometric correctness
 * Validates: Requirements 2.2
 *
 * Tests that isContained correctly determines whether a point (line, col)
 * falls within a span defined by (sL, sC) → (eL, eC).
 */

// Generator for valid spans: sL <= eL, and when sL==eL then sC <= eC
const spanArb = fc
  .tuple(
    fc.nat({ max: 1000 }),
    fc.nat({ max: 1000 }),
    fc.nat({ max: 1000 }),
    fc.nat({ max: 1000 }),
  )
  .map(([sL, sC, dL, dC]) => {
    const eL = sL + dL;
    const eC = sL === eL ? sC + dC : dC;
    return { sL, sC, eL, eC };
  });

describe("Property 2: Containment predicate geometric correctness", () => {
  it("a point at span start (sL, sC) is always contained", () => {
    fc.assert(
      fc.property(spanArb, ({ sL, sC, eL, eC }) => {
        expect(isContained(sL, sC, sL, sC, eL, eC)).toBe(true);
      }),
      { numRuns: 100 },
    );
  });

  it("a point at span end (eL, eC) is always contained", () => {
    fc.assert(
      fc.property(spanArb, ({ sL, sC, eL, eC }) => {
        expect(isContained(eL, eC, sL, sC, eL, eC)).toBe(true);
      }),
      { numRuns: 100 },
    );
  });

  it("a point before span start line is never contained", () => {
    fc.assert(
      fc.property(
        spanArb.filter(({ sL }) => sL > 0),
        fc.nat({ max: 1000 }),
        fc.nat({ max: 1000 }),
        ({ sL, sC, eL, eC }, offset, col) => {
          const line = sL - 1 - (offset % sL);
          expect(isContained(line, col, sL, sC, eL, eC)).toBe(false);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("a point after span end line is never contained", () => {
    fc.assert(
      fc.property(
        spanArb,
        fc.integer({ min: 1, max: 1000 }),
        fc.nat({ max: 1000 }),
        ({ sL, sC, eL, eC }, offset, col) => {
          const line = eL + offset;
          expect(isContained(line, col, sL, sC, eL, eC)).toBe(false);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("a point on start line but before start col is never contained", () => {
    fc.assert(
      fc.property(
        spanArb.filter(({ sC }) => sC > 0),
        fc.nat({ max: 1000 }),
        ({ sL, sC, eL, eC }, offset) => {
          const col = sC - 1 - (offset % sC);
          expect(isContained(sL, col, sL, sC, eL, eC)).toBe(false);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("a point on end line but after end col is never contained", () => {
    fc.assert(
      fc.property(
        spanArb,
        fc.integer({ min: 1, max: 1000 }),
        ({ sL, sC, eL, eC }, offset) => {
          const col = eC + offset;
          expect(isContained(eL, col, sL, sC, eL, eC)).toBe(false);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("a point strictly between start and end lines is always contained (any col)", () => {
    fc.assert(
      fc.property(
        spanArb.filter(({ sL, eL }) => eL - sL >= 2),
        fc.nat({ max: 10000 }),
        fc.nat({ max: 10000 }),
        ({ sL, sC, eL, eC }, offsetRaw, col) => {
          const range = eL - sL - 1; // at least 1
          const line = sL + 1 + (offsetRaw % range);
          expect(isContained(line, col, sL, sC, eL, eC)).toBe(true);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("single-line spans (sL==eL): contained iff sC <= col <= eC", () => {
    fc.assert(
      fc.property(
        fc.nat({ max: 1000 }),
        fc.nat({ max: 1000 }),
        fc.nat({ max: 1000 }),
        fc.nat({ max: 2000 }),
        (sL, sC, colRange, col) => {
          const eL = sL;
          const eC = sC + colRange; // ensures sC <= eC
          const expected = col >= sC && col <= eC;
          expect(isContained(sL, col, sL, sC, eL, eC)).toBe(expected);
        },
      ),
      { numRuns: 100 },
    );
  });
});

/**
 * Property 1: Span map collects all distinct range entries
 * Validates: Requirements 1.1, 1.2, 1.3
 *
 * For any prover log with N distinct range entries in assertion batches,
 * the parsed ProofGraph contains nodes with matching IDs for each range entry.
 * Since the span map is internal, we verify indirectly: every range entry that
 * appears in an assertion batch (Assertions/Proof dependencies/Unused) becomes
 * a node in the graph with ID = file:sL,sC-eL,eC.
 */

import { parseProof } from "../../../core/src/proof.js";

// Generator: simple file names (alphanumeric + ".dfy")
const arbFileName = fc
  .stringOf(fc.char().filter((c) => /[a-z0-9]/.test(c)), { minLength: 1, maxLength: 8 })
  .map((s) => s + ".dfy");

// Generator: valid coordinates where sL <= eL, and if sL==eL then sC < eC
const arbCoords = fc
  .record({
    sL: fc.integer({ min: 1, max: 100 }),
    sC: fc.integer({ min: 1, max: 100 }),
    dL: fc.integer({ min: 0, max: 20 }),
    dC: fc.integer({ min: 1, max: 50 }),
  })
  .map(({ sL, sC, dL, dC }) => {
    const eL = sL + dL;
    const eC = dL === 0 ? sC + dC : dC; // if same line, eC > sC
    return { sL, sC, eL, eC };
  });

// Pool of known messages that appear in range entries
const RANGE_MESSAGES = [
  "ensures clause",
  "requires clause at foo.dfy(1,2)-(1,5) from call",
  "loop invariant always holds",
  "assertion always holds",
  "index in range",
  "target object is never null",
  "some code line",
  "decreases expression is bounded below by 0",
];

const arbRangeMessage = fc.constantFrom(...RANGE_MESSAGES);

// A single range entry
interface RangeEntry {
  file: string;
  sL: number;
  sC: number;
  eL: number;
  eC: number;
  message: string;
}

// Generator: a list of distinct range entries (distinct by coordinates+file)
const arbRangeEntries = fc
  .array(
    fc.tuple(arbFileName, arbCoords, arbRangeMessage).map(([file, coords, message]) => ({
      file,
      sL: coords.sL,
      sC: coords.sC,
      eL: coords.eL,
      eC: coords.eC,
      message,
    })),
    { minLength: 1, maxLength: 10 },
  )
  .map((entries) => {
    // Deduplicate by ID to ensure distinct entries
    const seen = new Set<string>();
    const unique: RangeEntry[] = [];
    for (const e of entries) {
      const id = `${e.file}:${e.sL},${e.sC}-${e.eL},${e.eC}`;
      if (!seen.has(id)) {
        seen.add(id);
        unique.push(e);
      }
    }
    return unique;
  })
  .filter((entries) => entries.length >= 1);

/**
 * Build a prover log string with assertion batches containing the given range entries.
 * Each entry is placed in a "Proof dependencies:" block under a top assertion.
 */
function buildSpanMapLog(entries: RangeEntry[]): string {
  const lines: string[] = [];
  // Create one assertion batch with a top assertion, then put all entries in Proof dependencies
  lines.push("  Assertion batch 0:");
  lines.push("  Assertions:");
  // Use first entry's file for the top assertion point node
  const topFile = entries[0].file;
  lines.push(`    ${topFile}(1, 1)-(1, 5): assertion always holds`);
  lines.push("  Proof dependencies:");
  for (const e of entries) {
    lines.push(`    ${e.file}(${e.sL}, ${e.sC})-(${e.eL}, ${e.eC}): ${e.message}`);
  }
  return lines.join("\n");
}

describe("Property 1: Span map collects all distinct range entries", () => {
  it("every range entry in an assertion batch becomes a node in the graph with matching ID", () => {
    fc.assert(
      fc.property(arbRangeEntries, (entries) => {
        const log = buildSpanMapLog(entries);
        const proof = parseProof("", log);
        const allNodes = proof.proofGraph.getAllNodes();
        const nodeIds = new Set(allNodes.map((n) => n.id));

        for (const e of entries) {
          const expectedId = `${e.file}:${e.sL},${e.sC}-${e.eL},${e.eC}`;
          expect(nodeIds).toContain(expectedId);
        }
      }),
      { numRuns: 100 },
    );
  });

  it("node count is at least the number of distinct range entries", () => {
    fc.assert(
      fc.property(arbRangeEntries, (entries) => {
        const log = buildSpanMapLog(entries);
        const proof = parseProof("", log);
        const allNodes = proof.proofGraph.getAllNodes();
        // Graph has at least entries.length nodes (plus the top assertion node)
        expect(allNodes.length).toBeGreaterThanOrEqual(entries.length);
      }),
      { numRuns: 100 },
    );
  });

  it("each node's file and coordinates match the original range entry", () => {
    fc.assert(
      fc.property(arbRangeEntries, (entries) => {
        const log = buildSpanMapLog(entries);
        const proof = parseProof("", log);

        for (const e of entries) {
          const expectedId = `${e.file}:${e.sL},${e.sC}-${e.eL},${e.eC}`;
          const node = proof.proofGraph.getNode(expectedId);
          expect(node).toBeDefined();
          expect(node!.file).toBe(e.file);
          expect(node!.start.line).toBe(e.sL);
          expect(node!.start.col).toBe(e.sC);
          expect(node!.end.line).toBe(e.eL);
          expect(node!.end.col).toBe(e.eC);
        }
      }),
      { numRuns: 100 },
    );
  });
});

/**
 * Property 3: Point-to-range promotion on match
 * Validates: Requirements 2.1, 2.3
 *
 * For any prover log where a point-only top assertion at (L, C) has a matching
 * range entry in the span map (containment + message-class match), the resulting
 * ProofGraph SHALL contain a top node with the full range span instead of the point.
 */

// Message class configs: [topMessage, rangeMessage]
const MESSAGE_CLASS_PAIRS: Array<{ topMsg: string; rangeMsg: string }> = [
  { topMsg: "this postcondition holds", rangeMsg: "ensures clause" },
  { topMsg: "assertion always holds", rangeMsg: "assertion always holds" },
];

// Generator: valid span where sL <= eL, and if sL==eL then sC < eC (non-point)
const arbNonPointSpan = fc
  .record({
    sL: fc.integer({ min: 1, max: 50 }),
    sC: fc.integer({ min: 1, max: 80 }),
    dL: fc.integer({ min: 0, max: 10 }),
    dC: fc.integer({ min: 1, max: 40 }),
  })
  .map(({ sL, sC, dL, dC }) => {
    const eL = sL + dL;
    const eC = dL === 0 ? sC + dC : dC + 1; // ensure non-point: eC > sC on same line, or different lines
    return { sL, sC, eL, eC };
  });

// Generator: a point (L, C) contained within the given span
function arbPointInSpan(span: { sL: number; sC: number; eL: number; eC: number }) {
  const { sL, sC, eL, eC } = span;
  if (sL === eL) {
    // Single-line span: L = sL, sC <= C <= eC
    return fc.integer({ min: sC, max: eC }).map((c) => ({ L: sL, C: c }));
  }
  // Multi-line span: pick a line between sL and eL
  return fc.integer({ min: sL, max: eL }).chain((L) => {
    if (L === sL && L === eL) {
      return fc.integer({ min: sC, max: eC }).map((C) => ({ L, C }));
    } else if (L === sL) {
      return fc.nat().map((c) => ({ L, C: sC + c }));
    } else if (L === eL) {
      return fc.integer({ min: 0, max: eC }).map((C) => ({ L, C }));
    } else {
      return fc.nat().map((C) => ({ L, C }));
    }
  });
}

// Generator: message class pair
const arbMsgClass = fc.constantFrom(...MESSAGE_CLASS_PAIRS);

// Combined generator for the full scenario
const arbPromotionScenario = fc
  .record({
    span: arbNonPointSpan,
    msgClass: arbMsgClass,
    file: arbFileName,
  })
  .chain(({ span, msgClass, file }) =>
    arbPointInSpan(span).map((point) => ({
      span,
      point,
      msgClass,
      file,
    })),
  );

/**
 * Build a prover log with:
 * - Assertion batch containing a point-only top assertion at (L, C) with topMsg
 * - Proof dependencies block containing a range entry (sL,sC)-(eL,eC) with rangeMsg
 */
function buildPromotionLog(
  file: string,
  point: { L: number; C: number },
  span: { sL: number; sC: number; eL: number; eC: number },
  topMsg: string,
  rangeMsg: string,
): string {
  const lines: string[] = [];
  lines.push("  Assertion batch 0:");
  lines.push("  Assertions:");
  lines.push(`    ${file}(${point.L}, ${point.C}): ${topMsg}`);
  lines.push("  Proof dependencies:");
  lines.push(`    ${file}(${span.sL}, ${span.sC})-(${span.eL}, ${span.eC}): ${rangeMsg}`);
  return lines.join("\n");
}

describe("Property 3: Point-to-range promotion on match", () => {
  it("point-only top assertion is promoted to full range when matching span exists", () => {
    fc.assert(
      fc.property(arbPromotionScenario, ({ span, point, msgClass, file }) => {
        const log = buildPromotionLog(file, point, span, msgClass.topMsg, msgClass.rangeMsg);
        const proof = parseProof("", log);

        const expectedRangeId = `${file}:${span.sL},${span.sC}-${span.eL},${span.eC}`;
        const pointId = `${file}:${point.L},${point.C}-${point.L},${point.C}`;

        // The graph should have a top node with the full range ID
        const topNodes = proof.proofGraph.getAllTopNodes();
        const topIds = topNodes.map((n) => n.id);

        expect(topIds).toContain(expectedRangeId);
        // The point ID should NOT be a top node (it was promoted)
        expect(topIds).not.toContain(pointId);
      }),
      { numRuns: 100 },
    );
  });
});

/**
 * Property 4: Tightest containing span wins
 * Validates: Requirements 2.4
 *
 * For any point-only top assertion with TWO nested spans that both contain the
 * point and have matching message class, the parser selects the inner (tighter) span.
 */

// Generator: inner span (non-point)
const arbInnerSpan = fc
  .record({
    sL: fc.integer({ min: 2, max: 40 }),
    sC: fc.integer({ min: 2, max: 60 }),
    dL: fc.integer({ min: 0, max: 5 }),
    dC: fc.integer({ min: 1, max: 20 }),
  })
  .map(({ sL, sC, dL, dC }) => {
    const eL = sL + dL;
    const eC = dL === 0 ? sC + dC : dC + 1;
    return { sL, sC, eL, eC };
  });

// Generator: outer span that strictly contains the inner span
function arbOuterSpan(inner: { sL: number; sC: number; eL: number; eC: number }) {
  return fc
    .record({
      expandStartLine: fc.integer({ min: 0, max: 3 }),
      expandStartCol: fc.integer({ min: 0, max: 5 }),
      expandEndLine: fc.integer({ min: 0, max: 3 }),
      expandEndCol: fc.integer({ min: 0, max: 5 }),
    })
    .filter(({ expandStartLine, expandStartCol, expandEndLine, expandEndCol }) =>
      expandStartLine + expandStartCol + expandEndLine + expandEndCol > 0,
    )
    .map(({ expandStartLine, expandStartCol, expandEndLine, expandEndCol }) => ({
      sL: Math.max(1, inner.sL - expandStartLine),
      sC: Math.max(1, inner.sC - expandStartCol),
      eL: inner.eL + expandEndLine,
      eC: inner.eC + expandEndCol,
    }))
    .filter((outer) => {
      if (outer.sL > inner.sL || outer.eL < inner.eL) return false;
      if (outer.sL === inner.sL && outer.sC > inner.sC) return false;
      if (outer.eL === inner.eL && outer.eC < inner.eC) return false;
      const sameStart = outer.sL === inner.sL && outer.sC === inner.sC;
      const sameEnd = outer.eL === inner.eL && outer.eC === inner.eC;
      return !(sameStart && sameEnd);
    });
}

// Generator: point inside the inner span (reuse logic)
function arbPointInInnerSpan(inner: { sL: number; sC: number; eL: number; eC: number }) {
  if (inner.sL === inner.eL) {
    return fc.integer({ min: inner.sC, max: inner.eC }).map((c) => ({ L: inner.sL, C: c }));
  }
  return fc.integer({ min: inner.sL, max: inner.eL }).chain((L) => {
    if (L === inner.sL && L === inner.eL) {
      return fc.integer({ min: inner.sC, max: inner.eC }).map((C) => ({ L, C }));
    } else if (L === inner.sL) {
      return fc.nat().map((c) => ({ L, C: inner.sC + c }));
    } else if (L === inner.eL) {
      return fc.integer({ min: 0, max: inner.eC }).map((C) => ({ L, C }));
    } else {
      return fc.nat().map((C) => ({ L, C }));
    }
  });
}

// Combined generator for tightest-span scenario
const arbTightestScenario = arbInnerSpan.chain((inner) =>
  fc.tuple(arbOuterSpan(inner), arbPointInInnerSpan(inner), arbFileName).map(([outer, point, file]) => ({
    inner,
    outer,
    point,
    file,
  })),
);

function buildTightestSpanLog(
  file: string,
  point: { L: number; C: number },
  inner: { sL: number; sC: number; eL: number; eC: number },
  outer: { sL: number; sC: number; eL: number; eC: number },
): string {
  const lines: string[] = [];
  lines.push("  Assertion batch 0:");
  lines.push("  Assertions:");
  lines.push(`    ${file}(${point.L}, ${point.C}): assertion always holds`);
  lines.push("  Proof dependencies:");
  // Put outer first to ensure parser doesn't just pick first match
  lines.push(`    ${file}(${outer.sL}, ${outer.sC})-(${outer.eL}, ${outer.eC}): assertion always holds`);
  lines.push(`    ${file}(${inner.sL}, ${inner.sC})-(${inner.eL}, ${inner.eC}): assertion always holds`);
  return lines.join("\n");
}

describe("Property 4: Tightest containing span wins", () => {
  it("when two nested spans both contain the point, the inner (tighter) span is selected as top node", () => {
    fc.assert(
      fc.property(arbTightestScenario, ({ inner, outer, point, file }) => {
        const log = buildTightestSpanLog(file, point, inner, outer);
        const proof = parseProof("", log);

        const innerSpanId = `${file}:${inner.sL},${inner.sC}-${inner.eL},${inner.eC}`;
        const pointId = `${file}:${point.L},${point.C}-${point.L},${point.C}`;

        const topNodes = proof.proofGraph.getAllTopNodes();
        const topIds = topNodes.map((n) => n.id);

        // Top node should be the inner (tighter) span
        expect(topIds).toContain(innerSpanId);
        // Point should not remain as top
        expect(topIds).not.toContain(pointId);
      }),
      { numRuns: 100 },
    );
  });
});

/**
 * Property 5: No-match behavior (strict vs graceful)
 * Validates: Requirements 2.5
 *
 * When no span in the span map satisfies containment + message-class matching:
 * - In strict mode (NODE_ENV=test): an exception is thrown
 * - In non-strict mode: the node remains a point node
 *
 * Since tests run with NODE_ENV=test (STRICT_SPAN_MERGE=true), we test that
 * parsing a log with a point-only top assertion and NO matching range entry throws.
 */

describe("Property 5: No-match behavior", () => {
  it("strict mode throws when no matching span exists for a point-only top assertion", () => {
    fc.assert(
      fc.property(
        arbFileName,
        fc.integer({ min: 1, max: 100 }),
        fc.integer({ min: 1, max: 100 }),
        (file, line, col) => {
          // Log with a point-only top assertion but NO range entries with matching message
          const log = [
            "  Assertion batch 0:",
            "  Assertions:",
            `    ${file}(${line}, ${col}): this postcondition holds`,
            "  Proof dependencies:",
            // Range entry with NON-matching message class (precondition range for postcondition top)
            `    ${file}(${line}, ${col})-(${line}, ${col + 5}): requires clause at foo.dfy(1,1)-(1,5) from call`,
          ].join("\n");

          expect(() => parseProof("", log)).toThrow(/STRICT_SPAN_MERGE/);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("strict mode does NOT throw when a matching span exists", () => {
    fc.assert(
      fc.property(
        arbFileName,
        fc.integer({ min: 1, max: 100 }),
        fc.integer({ min: 1, max: 100 }),
        (file, line, col) => {
          // Log with matching range entry (postcondition → ensures clause)
          const log = [
            "  Assertion batch 0:",
            "  Assertions:",
            `    ${file}(${line}, ${col}): this postcondition holds`,
            "  Proof dependencies:",
            `    ${file}(${line}, ${col})-(${line}, ${col + 5}): ensures clause`,
          ].join("\n");

          expect(() => parseProof("", log)).not.toThrow();
        },
      ),
      { numRuns: 100 },
    );
  });
});

/**
 * Property 7: Promotion preserves node identity and graph connectivity
 * Validates: Requirements 2.6, 5.1, 5.2, 5.3, 5.4
 *
 * After promotion:
 * (a) ID = file:sL,sC-eL,eC (full range)
 * (b) Old point-based ID removed from node map
 * (c) New ID present in top-nodes map
 * (d) prooftext, isTopAssertion, type preserved
 * (e) Edges connect to the range node (proof deps are children of the top)
 */

describe("Property 7: Promotion preserves node identity and graph connectivity", () => {
  it("promoted node has correct ID, fields, and edges", () => {
    fc.assert(
      fc.property(
        arbNonPointSpan,
        arbFileName,
        (span, file) => {
          // Point at span start (always contained)
          const point = { L: span.sL, C: span.sC };
          const topMsg = "assertion always holds";
          const rangeMsg = "assertion always holds";

          // Add a child dependency node to verify edge connectivity
          const childLine = span.eL + 10;
          const log = [
            "  Assertion batch 0:",
            "  Assertions:",
            `    ${file}(${point.L}, ${point.C}): ${topMsg}`,
            "  Proof dependencies:",
            `    ${file}(${span.sL}, ${span.sC})-(${span.eL}, ${span.eC}): ${rangeMsg}`,
            `    ${file}(${childLine}, 1)-(${childLine}, 5): some dep`,
          ].join("\n");

          const proof = parseProof("", log);

          const rangeId = `${file}:${span.sL},${span.sC}-${span.eL},${span.eC}`;
          const pointId = `${file}:${point.L},${point.C}-${point.L},${point.C}`;

          // (a) Range ID exists in graph
          expect(proof.proofGraph.hasNode(rangeId)).toBe(true);
          // (b) Point ID removed (unless point === range start, in which case they're same node)
          if (pointId !== rangeId) {
            expect(proof.proofGraph.hasNode(pointId)).toBe(false);
          }
          // (c) Range ID is a top node
          expect(proof.proofGraph.hasTopNode(rangeId)).toBe(true);

          const node = proof.proofGraph.getNode(rangeId)!;
          // (d) Fields preserved
          expect(node.prooftext).toBe(topMsg);
          expect(node.isTopAssertion).toBe(true);

          // (e) Edge connectivity: child dep should be connected
          const childId = `${file}:${childLine},1-${childLine},5`;
          if (proof.proofGraph.hasNode(childId)) {
            expect(node.provedBy.size).toBeGreaterThanOrEqual(1);
            const childIds = [...node.provedBy].map((n) => n.id);
            expect(childIds).toContain(childId);
          }
        },
      ),
      { numRuns: 100 },
    );
  });
});

/**
 * Property 8: Range-only logs produce unchanged output
 * Validates: Requirements 4.4
 *
 * For logs where all top assertions already have full range data (no point-only tops),
 * the span-merging feature produces identical output to what would be produced without it.
 * We verify this by checking that range-only top assertions remain unchanged.
 */

describe("Property 8: Range-only logs produce unchanged output", () => {
  it("range-only top assertions are not modified by span merging", () => {
    fc.assert(
      fc.property(
        arbFileName,
        arbCoords,
        fc.constantFrom("assertion always holds", "this postcondition holds", "index in range"),
        (file, coords, msg) => {
          // Log where the top assertion already has a full range (not a point)
          const log = [
            "  Assertion batch 0:",
            "  Assertions:",
            `    ${file}(${coords.sL}, ${coords.sC})-(${coords.eL}, ${coords.eC}): ${msg}`,
            "  Proof dependencies:",
            `    ${file}(${coords.sL}, ${coords.sC})-(${coords.eL}, ${coords.eC}): ${msg}`,
          ].join("\n");

          const proof = parseProof("", log);

          const expectedId = `${file}:${coords.sL},${coords.sC}-${coords.eL},${coords.eC}`;
          const topNodes = proof.proofGraph.getAllTopNodes();
          const topIds = topNodes.map((n) => n.id);

          // The range-only top assertion should remain with its original ID
          expect(topIds).toContain(expectedId);
          // Only one top node should exist
          expect(topNodes.length).toBe(1);

          const node = proof.proofGraph.getNode(expectedId)!;
          expect(node.start.line).toBe(coords.sL);
          expect(node.start.col).toBe(coords.sC);
          expect(node.end.line).toBe(coords.eL);
          expect(node.end.col).toBe(coords.eC);
        },
      ),
      { numRuns: 100 },
    );
  });
});
