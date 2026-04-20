import { describe, it, expect } from "vitest";
import {
  computeConfusionMatrix,
  computeMetrics,
  formatTable,
  type ConfusionMatrix,
} from "../reporter.js";
import type { ClassificationResult } from "../classifier.js";

function makeResult(
  classification: "strong" | "weak" | "error",
  oracleLabel: "strong" | "weak"
): ClassificationResult {
  return {
    taskId: "t1",
    filePath: "/f.dfy",
    classification,
    oracleLabel,
    postconditionLines: [],
    bodyLines: [],
    coverageStatuses: {},
  };
}

describe("computeConfusionMatrix", () => {
  it("counts TP/FP/TN/FN correctly", () => {
    const results = [
      makeResult("strong", "strong"), // TP
      makeResult("strong", "weak"), // FP
      makeResult("weak", "weak"), // TN
      makeResult("weak", "strong"), // FN
    ];
    const cm = computeConfusionMatrix(results);
    expect(cm).toEqual({ tp: 1, fp: 1, tn: 1, fn: 1 });
  });

  it("excludes error-classified results", () => {
    const results = [
      makeResult("strong", "strong"),
      makeResult("error", "strong"),
      makeResult("error", "weak"),
    ];
    const cm = computeConfusionMatrix(results);
    expect(cm).toEqual({ tp: 1, fp: 0, tn: 0, fn: 0 });
  });

  it("returns all zeros for empty input", () => {
    expect(computeConfusionMatrix([])).toEqual({ tp: 0, fp: 0, tn: 0, fn: 0 });
  });
});

describe("computeMetrics", () => {
  it("computes standard metrics", () => {
    const cm: ConfusionMatrix = { tp: 40, fp: 10, tn: 30, fn: 20 };
    const m = computeMetrics(cm);
    expect(m.precision).toBeCloseTo(0.8, 5);
    expect(m.recall).toBeCloseTo(2 / 3, 5);
    expect(m.f1).toBeCloseTo((2 * 0.8 * (2 / 3)) / (0.8 + 2 / 3), 5);
    expect(m.accuracy).toBeCloseTo(0.7, 5);
  });

  it("handles zero denominators", () => {
    const cm: ConfusionMatrix = { tp: 0, fp: 0, tn: 0, fn: 0 };
    const m = computeMetrics(cm);
    expect(m.precision).toBe(0);
    expect(m.recall).toBe(0);
    expect(m.f1).toBe(0);
    expect(m.accuracy).toBe(0);
  });

  it("handles no positives predicted (precision denom zero)", () => {
    const cm: ConfusionMatrix = { tp: 0, fp: 0, tn: 5, fn: 3 };
    const m = computeMetrics(cm);
    expect(m.precision).toBe(0);
    expect(m.recall).toBe(0);
    expect(m.f1).toBe(0);
    expect(m.accuracy).toBeCloseTo(5 / 8, 5);
  });
});

describe("formatTable", () => {
  it("contains confusion matrix values and metrics", () => {
    const cm: ConfusionMatrix = { tp: 10, fp: 2, tn: 8, fn: 5 };
    const metrics = computeMetrics(cm);
    const table = formatTable(cm, metrics);
    expect(table).toContain("10");
    expect(table).toContain("2");
    expect(table).toContain("8");
    expect(table).toContain("5");
    expect(table).toContain("Precision");
    expect(table).toContain("Recall");
    expect(table).toContain("F1");
    expect(table).toContain("Accuracy");
  });
});
