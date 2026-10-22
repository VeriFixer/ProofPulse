import { describe, it, expect } from "vitest";
import { Classification, OracleLabel } from "../../../evaluation/src/types.js";
import {
  formatInteractiveOutput,
  type InteractiveStep,
} from "../../../evaluation/src/interactive.js";

function makeStep(overrides?: Partial<InteractiveStep>): InteractiveStep {
  return {
    filePath: "test/file.dfy",
    coverageJson: { line1: "CovComplete" },
    classification: Classification.Strong,
    oracleLabel: OracleLabel.Strong,
    pass: true,
    ...overrides,
  };
}

describe("formatInteractiveOutput", () => {
  it("includes file path", () => {
    const out = formatInteractiveOutput(makeStep());
    expect(out).toContain("Running proof_coverage on file test/file.dfy...");
  });

  it("includes coverage JSON", () => {
    const step = makeStep({ coverageJson: { a: 1 } });
    const out = formatInteractiveOutput(step);
    expect(out).toContain(JSON.stringify({ a: 1 }, null, 2));
  });

  it("includes classification and oracle label", () => {
    const out = formatInteractiveOutput(makeStep({ classification: Classification.Weak, oracleLabel: OracleLabel.Weak }));
    expect(out).toContain("Classification: weak");
    expect(out).toContain("Oracle classification: weak");
  });

  it("shows PASS when pass is true", () => {
    const out = formatInteractiveOutput(makeStep({ pass: true }));
    expect(out).toContain("PASS");
  });

  it("shows FAIL when pass is false", () => {
    const out = formatInteractiveOutput(makeStep({ pass: false }));
    expect(out).toContain("FAIL");
  });

  it("handles error classification", () => {
    const out = formatInteractiveOutput(makeStep({ classification: Classification.Error }));
    expect(out).toContain("Classification: error");
  });
});
