import { describe, it, expect } from "vitest";
import {
  validateClassificationResult,
  truncateSource,
  generateReport,
  generateSummary,
  type AgentClassificationResult,
} from "../agent-helpers.js";

// --- validateClassificationResult edge cases ---

describe("validateClassificationResult", () => {
  const validObj: AgentClassificationResult = {
    dataset: "RQ1-GPT4",
    taskId: "126",
    category: "postcondition",
    direction: "FP",
    predicted: "strong",
    oracle: "weak",
    rootCause: "quantifier_not_tracked",
    explanation: "quantifier not tracked by coverage model",
    confidence: 0.85,
    oracleError: false,
    relativePath: ".eval-tmp/RQ1-GPT4/task_id_126.dfy",
    logPath: ".eval-tmp/logs/RQ1-GPT4/task_id_126.log.txt",
  };

  it("rejects null", () => {
    expect(validateClassificationResult(null)).toBe(false);
  });

  it("rejects non-object: number", () => {
    expect(validateClassificationResult(42)).toBe(false);
  });

  it("rejects non-object: string", () => {
    expect(validateClassificationResult("hello")).toBe(false);
  });

  it("rejects non-object: array", () => {
    expect(validateClassificationResult([1, 2, 3])).toBe(false);
  });

  it("rejects object missing dataset field", () => {
    const { dataset, ...rest } = validObj;
    expect(validateClassificationResult(rest)).toBe(false);
  });

  it("rejects object with invalid rootCause value", () => {
    expect(validateClassificationResult({ ...validObj, rootCause: "bad_cause" })).toBe(false);
  });

  it("rejects object with confidence > 1", () => {
    expect(validateClassificationResult({ ...validObj, confidence: 1.5 })).toBe(false);
  });

  it("rejects object with confidence < 0", () => {
    expect(validateClassificationResult({ ...validObj, confidence: -0.1 })).toBe(false);
  });

  it("rejects object with confidence = NaN", () => {
    expect(validateClassificationResult({ ...validObj, confidence: NaN })).toBe(false);
  });

  it("rejects object with invalid category", () => {
    expect(validateClassificationResult({ ...validObj, category: "loop" })).toBe(false);
  });

  it("rejects object with invalid direction", () => {
    expect(validateClassificationResult({ ...validObj, direction: "TP" })).toBe(false);
  });

  it("rejects object with logPath as number (not string or null)", () => {
    expect(validateClassificationResult({ ...validObj, logPath: 123 })).toBe(false);
  });

  it("accepts valid object with logPath = null", () => {
    expect(validateClassificationResult({ ...validObj, logPath: null })).toBe(true);
  });

  it("accepts valid object with logPath = string", () => {
    expect(validateClassificationResult(validObj)).toBe(true);
  });
});

// --- truncateSource edge cases ---

describe("truncateSource", () => {
  it("returns unchanged if source has fewer lines than max", () => {
    const source = "line1\nline2\nline3";
    expect(truncateSource(source, 10)).toBe(source);
  });

  it("with empty string returns empty string", () => {
    expect(truncateSource("", 5)).toBe("");
  });
});

// --- generateReport with empty input ---

describe("generateReport", () => {
  it("with empty classifications returns header only", () => {
    const report = generateReport([]);
    expect(report).toContain("# Agent Divergence Classification Report");
    expect(report).toContain("Total classifications: 0");
    // No table rows
    expect(report).not.toContain("| RQ");
  });
});

// --- generateSummary with empty input ---

describe("generateSummary", () => {
  it("with empty classifications returns header only (with TOTAL | 0)", () => {
    const summary = generateSummary([]);
    expect(summary).toContain("TOTAL");
    expect(summary).toContain("| 0");
  });
});
