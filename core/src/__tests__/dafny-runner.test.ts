import { describe, expect, it } from "vitest";
import { finishedMethodsLog, mergeLogs } from "../backends/dafny/runner.js";

const block = (name: string, outcome = "Valid") =>
  `\nResults for ${name} (correctness)\n  Overall outcome: ${outcome}\n`;

describe("finishedMethodsLog", () => {
  it("keeps only the blocks before the last header while output flows", () => {
    const out = block("A") + block("B");
    expect(finishedMethodsLog(out, false)).toBe(block("A") + "\n");
  });

  it("keeps everything once output pauses", () => {
    const out = block("A") + block("B");
    expect(finishedMethodsLog(out, true)).toBe(out);
  });

  it("is empty before any method finished", () => {
    expect(finishedMethodsLog(block("A"), false)).toBe("");
    expect(finishedMethodsLog("Warning: something\n", true)).toBe("");
  });
});

describe("mergeLogs", () => {
  it("replaces the methods the newer log has and keeps the rest", () => {
    const base = block("A") + block("B") + block("C");
    const merged = mergeLogs(base, block("B", "Errors"));
    expect(merged).toContain("Results for A (correctness)\n  Overall outcome: Valid");
    expect(merged).toContain("Results for B (correctness)\n  Overall outcome: Errors");
    expect(merged).toContain("Results for C (correctness)\n  Overall outcome: Valid");
    expect(merged.match(/Results for B/g)).toHaveLength(1);
  });

  it("adds methods only the newer log has", () => {
    expect(mergeLogs(block("A"), block("D"))).toContain("Results for D");
  });
});

