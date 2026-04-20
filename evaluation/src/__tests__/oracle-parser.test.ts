import { describe, it, expect, vi } from "vitest";
import * as path from "node:path";
import * as fs from "node:fs";
import { parseOracle, parseAllOracles } from "../oracle-parser.js";

const REPO_ROOT = path.resolve(__dirname, "../../../dafny-synthesis");

describe("parseOracle", () => {
  it("returns entries with valid structure", () => {
    const entries = parseOracle(REPO_ROOT, "RQ3-GPT4");
    expect(entries.length).toBeGreaterThan(0);

    for (const entry of entries) {
      expect(entry.taskId).toBeTruthy();
      expect(entry.filePath).toBeTruthy();
      expect(["strong", "weak"]).toContain(entry.label);
      expect(path.isAbsolute(entry.filePath)).toBe(true);
      expect(fs.existsSync(entry.filePath)).toBe(true);
    }
  });

  it("RQ3-GPT4 matches paper: ~103 strong, ~11 weak postconditions", () => {
    const entries = parseOracle(REPO_ROOT, "RQ3-GPT4");
    const strong = entries.filter((e) => e.label === "strong").length;
    const weak = entries.filter((e) => e.label === "weak").length;
    expect(strong).toBe(103);
    expect(weak).toBeGreaterThanOrEqual(11);
  });

  it("RQ1-GPT4 has more spread: strong + weak + wrong", () => {
    const entries = parseOracle(REPO_ROOT, "RQ1-GPT4");
    const strong = entries.filter((e) => e.label === "strong").length;
    const weak = entries.filter((e) => e.label === "weak").length;
    // Paper: 34 strong, 15 weak, 7 wrong = 22 non-strong
    expect(strong).toBeGreaterThan(0);
    expect(weak).toBeGreaterThan(0);
  });

  it("extracts per-category labels", () => {
    const entries = parseOracle(REPO_ROOT, "RQ3-GPT4");
    const withInv = entries.filter((e) => e.labels.invariant != null);
    const withPre = entries.filter((e) => e.labels.precondition != null);
    expect(withInv.length).toBeGreaterThan(0);
    expect(withPre.length).toBeGreaterThan(0);
  });

  it("has no duplicate task IDs within a dataset", () => {
    const entries = parseOracle(REPO_ROOT, "RQ3-GPT4");
    const taskIds = entries.map((e) => e.taskId);
    expect(new Set(taskIds).size).toBe(taskIds.length);
  });

  it("parseAllOracles returns all 6 datasets", () => {
    const all = parseAllOracles(REPO_ROOT);
    expect(all.size).toBe(6);
  });
});
