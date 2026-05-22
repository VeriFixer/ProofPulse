import { describe, it, expect } from "vitest";
import fc from "fast-check";
import {
  buildLogPath,
  prepareContext,
  validateClassificationResult,
  identifyDivergences,
  generateSummary,
  generateReport,
  truncateSource,
  type AgentClassificationResult,
  type DivergenceInfo,
  type RootCause,
} from "../agent-helpers.js";
import type { ClassificationResult, CategoryClassification } from "../classifier.js";
import type { OracleEntry } from "../oracle-parser.js";

// --- Arbitraries ---

const arbRootCause: fc.Arbitrary<RootCause> = fc.constantFrom(
  "quantifier_not_tracked",
  "trivially_true_spec",
  "oracle_error",
  "multi_method",
  "tool_limitation",
  "insufficient_coverage_model",
  "other",
);

const arbCategory = fc.constantFrom("postcondition" as const, "precondition" as const, "invariant" as const);
const arbDirection = fc.constantFrom("FP" as const, "FN" as const);

const arbAgentClassificationResult: fc.Arbitrary<AgentClassificationResult> = fc.record({
  dataset: fc.string({ minLength: 1, maxLength: 20 }),
  taskId: fc.string({ minLength: 1, maxLength: 10 }),
  category: arbCategory,
  direction: arbDirection,
  predicted: fc.string({ minLength: 1, maxLength: 10 }),
  oracle: fc.string({ minLength: 1, maxLength: 10 }),
  rootCause: arbRootCause,
  explanation: fc.string({ minLength: 1, maxLength: 50 }),
  confidence: fc.double({ min: 0, max: 1, noNaN: true }),
  oracleError: fc.boolean(),
  relativePath: fc.string({ minLength: 1, maxLength: 30 }).map((s) => s + ".dfy"),
  logPath: fc.oneof(fc.constant(null), fc.string({ minLength: 1, maxLength: 30 }).map((s) => s + ".log.txt")),
});

const arbDivergenceInfo: fc.Arbitrary<DivergenceInfo> = fc.record({
  dataset: fc.string({ minLength: 1, maxLength: 20 }),
  taskId: fc.string({ minLength: 1, maxLength: 10 }),
  category: arbCategory,
  direction: arbDirection,
  predicted: fc.string({ minLength: 1, maxLength: 10 }),
  oracle: fc.string({ minLength: 1, maxLength: 10 }),
  source: fc.string({ minLength: 0, maxLength: 200 }),
  coverageStatuses: fc.dictionary(
    fc.integer({ min: 1, max: 100 }).map(String),
    fc.constantFrom("CovComplete", "CovTest", "Uncovered"),
  ),
  proofPulseLog: fc.oneof(fc.constant(null), fc.string({ minLength: 1, maxLength: 100 })),
});


// --- Property 1: Log path construction ---
describe("Property 1: Log path construction", () => {
  /**
   * Validates: Requirements 1.2, 1.3
   */
  it("buildLogPath produces correct path pattern for any dataset and .dfy filename", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 30 }).filter((s) => !s.includes("/") && !s.includes("\\")),
        fc.string({ minLength: 1, maxLength: 30 }).filter((s) => !s.includes("/") && !s.includes("\\")),
        (dataset, baseName) => {
          const filename = baseName + ".dfy";
          const result = buildLogPath(dataset, filename);
          expect(result).toBe(`.eval-tmp/logs/${dataset}/${baseName}.log.txt`);
        },
      ),
      { numRuns: 100 },
    );
  });
});

// --- Property 2: Context preparation completeness ---
describe("Property 2: Context preparation completeness", () => {
  /**
   * Validates: Requirements 2.2, 2.5
   */
  it("prepareContext output contains all required sections and values", () => {
    fc.assert(
      fc.property(arbDivergenceInfo, (divergence) => {
        const result = prepareContext(divergence);
        expect(result).toContain("=== SOURCE ===");
        expect(result).toContain("=== COVERAGE ===");
        expect(result).toContain("=== LABELS ===");
        expect(result).toContain("=== LOG ===");
        expect(result).toContain(divergence.predicted);
        expect(result).toContain(divergence.oracle);
        expect(result).toContain(divergence.category);
      }),
      { numRuns: 100 },
    );
  });
});

// --- Property 3: Validation accepts valid, rejects invalid ---
describe("Property 3: Classification result validation", () => {
  /**
   * Validates: Requirements 4.1, 4.2, 2.3
   */
  it("validateClassificationResult accepts valid objects", () => {
    fc.assert(
      fc.property(arbAgentClassificationResult, (obj) => {
        expect(validateClassificationResult(obj)).toBe(true);
      }),
      { numRuns: 100 },
    );
  });

  it("validateClassificationResult rejects objects with missing/invalid fields", () => {
    const arbInvalid = fc.oneof(
      // missing dataset
      fc.record({
        taskId: fc.string(),
        category: arbCategory,
        direction: arbDirection,
        predicted: fc.string(),
        oracle: fc.string(),
        rootCause: arbRootCause,
        explanation: fc.string(),
        confidence: fc.double({ min: 0, max: 1, noNaN: true }),
        oracleError: fc.boolean(),
        relativePath: fc.string(),
        logPath: fc.constant(null),
      }),
      // invalid confidence (> 1)
      arbAgentClassificationResult.map((o) => ({ ...o, confidence: 1.5 })),
      // invalid confidence (< 0)
      arbAgentClassificationResult.map((o) => ({ ...o, confidence: -0.1 })),
      // invalid category
      arbAgentClassificationResult.map((o) => ({ ...o, category: "invalid" })),
      // invalid rootCause
      arbAgentClassificationResult.map((o) => ({ ...o, rootCause: "bad_cause" })),
      // null object
      fc.constant(null),
      // non-object
      fc.constant(42),
    );

    fc.assert(
      fc.property(arbInvalid, (obj) => {
        expect(validateClassificationResult(obj)).toBe(false);
      }),
      { numRuns: 100 },
    );
  });
});


// --- Property 4: Divergence identification correctness ---
describe("Property 4: Divergence identification correctness", () => {
  /**
   * Validates: Requirements 3.2
   */
  it("identifyDivergences returns exactly entries where predicted != oracle", () => {
    const arbPostLabel = fc.constantFrom("strong" as const, "weak" as const);
    const arbPreLabel = fc.constantFrom("required" as const, "optional" as const);
    const arbInvLabel = fc.constantFrom("strong" as const, "weak" as const);

    const arbCategoryClassification: fc.Arbitrary<CategoryClassification> = fc.record({
      postcondition: fc.constantFrom("strong" as const, "weak" as const, "none" as const),
      precondition: fc.constantFrom("required" as const, "optional" as const, "none" as const),
      invariant: fc.constantFrom("strong" as const, "weak" as const, "none" as const),
    });

    const arbClassResult = fc.record({
      taskId: fc.integer({ min: 1, max: 999 }).map(String),
      filePath: fc.constant("/tmp/test.dfy"),
      classification: fc.constantFrom("strong" as const, "weak" as const),
      categories: arbCategoryClassification,
      oracleLabel: fc.constantFrom("strong" as const, "weak" as const, "wrong" as const),
      postconditionLines: fc.constant([] as number[]),
      preconditionLines: fc.constant([] as number[]),
      invariantLines: fc.constant([] as number[]),
      bodyLines: fc.constant([] as number[]),
      coverageStatuses: fc.constant({} as Record<number, any>),
    });

    const arbOracleEntry = fc.record({
      taskId: fc.integer({ min: 1, max: 999 }).map(String),
      filePath: fc.constant("/tmp/test.dfy"),
      label: fc.constantFrom("strong" as const, "weak" as const, "wrong" as const),
      labels: fc.record({
        postcondition: fc.oneof(fc.constant(undefined), arbPostLabel, fc.constant("wrong" as const)),
        precondition: fc.oneof(fc.constant(undefined), arbPreLabel),
        invariant: fc.oneof(fc.constant(undefined), arbInvLabel),
      }),
      dataset: fc.constant("RQ1-GPT4"),
      dafnyCode: fc.constant("method Foo() {}"),
    });

    fc.assert(
      fc.property(
        fc.array(arbClassResult, { minLength: 1, maxLength: 5 }),
        fc.array(arbOracleEntry, { minLength: 1, maxLength: 5 }),
        (results, oracles) => {
          // Build oracle map keyed by taskId
          const oracleMap = new Map<string, OracleEntry>();
          for (const o of oracles) {
            oracleMap.set(o.taskId, o as OracleEntry);
          }

          const divergences = identifyDivergences(results as ClassificationResult[], oracleMap);

          // Manually compute expected divergences
          const expected: Array<{ taskId: string; category: string; direction: string }> = [];
          for (const r of results) {
            if (r.classification === "error") continue;
            const oracle = oracleMap.get(r.taskId);
            if (!oracle) continue;

            // Postcondition
            if (oracle.labels.postcondition && oracle.labels.postcondition !== "wrong" && r.categories.postcondition !== "none") {
              const pred = r.categories.postcondition === "strong";
              const actual = oracle.labels.postcondition === "strong";
              if (pred !== actual) {
                expected.push({ taskId: r.taskId, category: "postcondition", direction: pred ? "FP" : "FN" });
              }
            }

            // Precondition
            if (oracle.labels.precondition && r.categories.precondition !== "none") {
              const pred = r.categories.precondition === "required";
              const actual = oracle.labels.precondition === "required";
              if (pred !== actual) {
                expected.push({ taskId: r.taskId, category: "precondition", direction: pred ? "FP" : "FN" });
              }
            }

            // Invariant
            if (oracle.labels.invariant && r.categories.invariant !== "none") {
              const pred = r.categories.invariant === "strong";
              const actual = oracle.labels.invariant === "strong";
              if (pred !== actual) {
                expected.push({ taskId: r.taskId, category: "invariant", direction: pred ? "FP" : "FN" });
              }
            }
          }

          expect(divergences.length).toBe(expected.length);
          for (const exp of expected) {
            const found = divergences.some(
              (d) => d.taskId === exp.taskId && d.category === exp.category && d.direction === exp.direction,
            );
            expect(found).toBe(true);
          }
        },
      ),
      { numRuns: 100 },
    );
  });
});

// --- Property 5: Summary counts match input ---
describe("Property 5: Summary counts correctness", () => {
  /**
   * Validates: Requirements 3.5
   */
  it("generateSummary contains correct count for each rootCause", () => {
    fc.assert(
      fc.property(
        fc.array(arbAgentClassificationResult, { minLength: 0, maxLength: 20 }),
        (classifications) => {
          const summary = generateSummary(classifications);

          // Count occurrences of each rootCause
          const counts = new Map<RootCause, number>();
          for (const c of classifications) {
            counts.set(c.rootCause, (counts.get(c.rootCause) ?? 0) + 1);
          }

          for (const [cause, count] of counts) {
            expect(summary).toContain(`${cause}`);
            expect(summary).toContain(`| ${count}`);
          }
        },
      ),
      { numRuns: 100 },
    );
  });
});


// --- Property 6: Report entry completeness ---
describe("Property 6: Report entry completeness", () => {
  /**
   * Validates: Requirements 5.2, 5.3, 5.5
   */
  it("generateReport contains links to .dfy file and log file for entries with non-null logPath", () => {
    const arbWithLog = arbAgentClassificationResult.map((o) => ({
      ...o,
      relativePath: `path/to/task_${o.taskId}.dfy`,
      logPath: `.eval-tmp/logs/dataset/task_${o.taskId}.log.txt`,
    }));

    fc.assert(
      fc.property(
        fc.array(arbWithLog, { minLength: 1, maxLength: 10 }),
        (classifications) => {
          const report = generateReport(classifications);

          for (const c of classifications) {
            // Should contain link to .dfy file
            expect(report).toContain(c.relativePath);
            // Should contain link to log file
            expect(report).toContain(c.logPath!);
          }
        },
      ),
      { numRuns: 100 },
    );
  });
});

// --- Property 7: Report grouping correctness ---
describe("Property 7: Report grouping correctness", () => {
  /**
   * Validates: Requirements 5.4
   */
  it("generateReport groups entries by rootCause — each entry in exactly one section", () => {
    fc.assert(
      fc.property(
        fc.array(arbAgentClassificationResult, { minLength: 1, maxLength: 15 }),
        (classifications) => {
          const report = generateReport(classifications);

          // Each rootCause that appears should have a section header
          const rootCauses = new Set(classifications.map((c) => c.rootCause));
          for (const cause of rootCauses) {
            expect(report).toContain(`## ${cause}`);
          }

          // Each entry's taskId should appear in the report
          for (const c of classifications) {
            expect(report).toContain(c.taskId);
          }

          // Count occurrences of each entry's taskId+category+direction combo in table rows
          // Each should appear exactly once
          for (const c of classifications) {
            const pattern = `| ${c.dataset} | ${c.taskId} | ${c.category} | ${c.direction} |`;
            const occurrences = report.split(pattern).length - 1;
            expect(occurrences).toBe(1);
          }
        },
      ),
      { numRuns: 100 },
    );
  });
});

// --- Property 8: Truncation preserves spec lines ---
describe("Property 8: Source truncation preserves spec lines", () => {
  /**
   * Validates: Requirements 6.2
   */
  it("truncateSource output has at most maxLines and contains spec lines", () => {
    const specKeywords = ["ensures", "requires", "invariant"];
    const arbLine = fc.oneof(
      fc.constantFrom(
        "  ensures x > 0",
        "  requires y != null",
        "  invariant i < n",
      ),
      fc.string({ minLength: 0, maxLength: 50 }).filter((s) => !specKeywords.some((k) => s.includes(k))),
    );

    fc.assert(
      fc.property(
        fc.array(arbLine, { minLength: 1, maxLength: 50 }),
        fc.integer({ min: 1, max: 50 }),
        (lines, maxLines) => {
          const source = lines.join("\n");
          const result = truncateSource(source, maxLines);
          const resultLines = result.split("\n");

          // (a) at most maxLines lines
          expect(resultLines.length).toBeLessThanOrEqual(maxLines);

          // (b) contains all spec lines from original (up to max limit)
          const specPattern = /\b(ensures|requires|invariant)\b/;
          const originalSpecLines = lines.filter((l) => specPattern.test(l));
          const keptSpecLines = resultLines.filter((l) => specPattern.test(l));

          // All spec lines should be preserved if they fit within budget
          const expectedSpecCount = Math.min(originalSpecLines.length, maxLines);
          expect(keptSpecLines.length).toBe(expectedSpecCount);
        },
      ),
      { numRuns: 100 },
    );
  });
});
