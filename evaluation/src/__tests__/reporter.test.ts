import { describe, it, expect } from "vitest";
import { computeConfusionMatrix, computeMetrics, formatTable, type ConfusionMatrix } from "../reporter.js";
import type { ClassificationResult } from "../classifier.js";
import { Classification, OracleLabel, PreconditionNeed, SpecStrength } from "../types.js";

const POST_FOR: Record<Classification, SpecStrength> = {
  [Classification.Strong]: SpecStrength.Strong,
  [Classification.Weak]: SpecStrength.Weak,
  [Classification.Error]: SpecStrength.None,
};

function makeResult(classification: Classification, oracleLabel: OracleLabel): ClassificationResult {
  return {
    taskId: "t1", filePath: "/f.dfy", classification, oracleLabel,
    categories: { postcondition: POST_FOR[classification], precondition: PreconditionNeed.None, invariant: SpecStrength.None },
    postconditionLines: [], preconditionLines: [], invariantLines: [], bodyLines: [], coverageStatuses: {},
  };
}

describe("computeConfusionMatrix", () => {
  it("counts TP/FP/TN/FN correctly", () => {
    const results = [makeResult(Classification.Strong, OracleLabel.Strong), makeResult(Classification.Strong, OracleLabel.Weak), makeResult(Classification.Weak, OracleLabel.Weak), makeResult(Classification.Weak, OracleLabel.Strong)];
    expect(computeConfusionMatrix(results)).toEqual({ tp: 1, fp: 1, tn: 1, fn: 1 });
  });
  it("excludes error results", () => {
    const results = [makeResult(Classification.Strong, OracleLabel.Strong), makeResult(Classification.Error, OracleLabel.Strong)];
    expect(computeConfusionMatrix(results)).toEqual({ tp: 1, fp: 0, tn: 0, fn: 0 });
  });
  it("excludes oracle=wrong results", () => {
    const results = [makeResult(Classification.Strong, OracleLabel.Strong), makeResult(Classification.Strong, OracleLabel.Wrong), makeResult(Classification.Weak, OracleLabel.Wrong)];
    expect(computeConfusionMatrix(results)).toEqual({ tp: 1, fp: 0, tn: 0, fn: 0 });
  });
  it("returns zeros for empty", () => {
    expect(computeConfusionMatrix([])).toEqual({ tp: 0, fp: 0, tn: 0, fn: 0 });
  });
});

describe("computeMetrics", () => {
  it("computes standard metrics", () => {
    const cm: ConfusionMatrix = { tp: 40, fp: 10, tn: 30, fn: 20 };
    const m = computeMetrics(cm);
    expect(m.precision).toBeCloseTo(0.8, 5);
    expect(m.recall).toBeCloseTo(2 / 3, 5);
    expect(m.accuracy).toBeCloseTo(0.7, 5);
  });
  it("handles zero denominators", () => {
    const m = computeMetrics({ tp: 0, fp: 0, tn: 0, fn: 0 });
    expect(m.precision).toBe(0);
    expect(m.recall).toBe(0);
    expect(m.f1).toBe(0);
    expect(m.accuracy).toBe(0);
  });
});

describe("formatTable", () => {
  it("contains values and labels", () => {
    const cm: ConfusionMatrix = { tp: 10, fp: 2, tn: 8, fn: 5 };
    const table = formatTable(cm, computeMetrics(cm));
    expect(table).toContain("10");
    expect(table).toContain("Precision");
  });
});
