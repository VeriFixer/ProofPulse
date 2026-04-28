import { describe, it, expect } from "vitest";
import { computeComparisonMetrics } from "../benchmark-runner.js";

describe("computeComparisonMetrics", () => {
  it("counts changed classifications", () => {
    const result = computeComparisonMetrics(
      ["strong", "weak", "error"],
      ["strong", "strong", "error"],
      [100, 200, 300],
      [110, 210, 310],
    );
    expect(result.changedResults).toBe(1);
  });

  it("computes addedTimeMs as minimized total minus baseline total", () => {
    const result = computeComparisonMetrics(
      ["strong", "weak"],
      ["strong", "weak"],
      [100, 200],
      [150, 250],
    );
    expect(result.addedTimeMs).toBe(100);
    expect(result.baselineTotalMs).toBe(300);
    expect(result.minimizedTotalMs).toBe(400);
  });

  it("computes slowdownFactor as ratio of totals", () => {
    const result = computeComparisonMetrics(
      ["strong"],
      ["strong"],
      [200],
      [400],
    );
    expect(result.slowdownFactor).toBe(2);
  });

  it("returns slowdownFactor 0 when baseline total is 0", () => {
    const result = computeComparisonMetrics(
      ["strong"],
      ["strong"],
      [0],
      [100],
    );
    expect(result.slowdownFactor).toBe(0);
  });

  it("handles empty arrays", () => {
    const result = computeComparisonMetrics([], [], [], []);
    expect(result.changedResults).toBe(0);
    expect(result.addedTimeMs).toBe(0);
    expect(result.slowdownFactor).toBe(0);
  });
});
