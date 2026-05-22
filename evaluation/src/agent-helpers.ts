/**
 * Agent divergence classification helpers.
 * Pure functions for context preparation, validation, divergence identification, and reporting.
 */
import * as path from "node:path";

import type { ClassificationResult } from "./classifier.js";
import type { OracleEntry } from "./oracle-parser.js";

// --- Types (2.1) ---

export type RootCause =
  | "quantifier_not_tracked"
  | "trivially_true_spec"
  | "oracle_error"
  | "multi_method"
  | "tool_limitation"
  | "insufficient_coverage_model"
  | "other";

export interface AgentClassificationResult {
  dataset: string;
  taskId: string;
  category: "postcondition" | "precondition" | "invariant";
  direction: "FP" | "FN";
  predicted: string;
  oracle: string;
  rootCause: RootCause;
  explanation: string;
  confidence: number; // 0-1
  oracleError: boolean;
  relativePath: string;
  logPath: string | null;
}

export interface DivergenceInfo {
  dataset: string;
  taskId: string;
  category: "postcondition" | "precondition" | "invariant";
  direction: "FP" | "FN";
  predicted: string;
  oracle: string;
  source: string;
  coverageStatuses: Record<number, string>;
  proofPulseLog: string | null;
}

// --- Validation (2.2) ---

const VALID_ROOT_CAUSES: RootCause[] = [
  "quantifier_not_tracked",
  "trivially_true_spec",
  "oracle_error",
  "multi_method",
  "tool_limitation",
  "insufficient_coverage_model",
  "other",
];

const VALID_CATEGORIES = ["postcondition", "precondition", "invariant"] as const;
const VALID_DIRECTIONS = ["FP", "FN"] as const;

export function validateClassificationResult(obj: unknown): obj is AgentClassificationResult {
  if (obj === null || typeof obj !== "object") return false;
  const o = obj as Record<string, unknown>;

  if (typeof o.dataset !== "string") return false;
  if (typeof o.taskId !== "string") return false;
  if (!VALID_CATEGORIES.includes(o.category as typeof VALID_CATEGORIES[number])) return false;
  if (!VALID_DIRECTIONS.includes(o.direction as typeof VALID_DIRECTIONS[number])) return false;
  if (typeof o.predicted !== "string") return false;
  if (typeof o.oracle !== "string") return false;
  if (!VALID_ROOT_CAUSES.includes(o.rootCause as RootCause)) return false;
  if (typeof o.explanation !== "string") return false;
  if (typeof o.confidence !== "number" || Number.isNaN(o.confidence) || o.confidence < 0 || o.confidence > 1) return false;
  if (typeof o.oracleError !== "boolean") return false;
  if (typeof o.relativePath !== "string") return false;
  if (o.logPath !== null && typeof o.logPath !== "string") return false;

  return true;
}

// --- Log path (2.3) ---

export function buildLogPath(dataset: string, filename: string): string {
  const base = filename.replace(/\.dfy$/, "");
  return `.eval-tmp/logs/${dataset}/${base}.log.txt`;
}

// --- Context preparation (2.4) ---

export function prepareContext(divergence: DivergenceInfo): string {
  const sections: string[] = [];

  sections.push("=== SOURCE ===");
  sections.push(divergence.source);

  sections.push("");
  sections.push("=== COVERAGE ===");
  const coverageLines = Object.entries(divergence.coverageStatuses)
    .map(([line, status]) => `L${line}: ${status}`)
    .join("\n");
  sections.push(coverageLines);

  sections.push("");
  sections.push("=== LABELS ===");
  sections.push(`Category: ${divergence.category}`);
  sections.push(`Direction: ${divergence.direction}`);
  sections.push(`Predicted: ${divergence.predicted}`);
  sections.push(`Oracle: ${divergence.oracle}`);

  sections.push("");
  sections.push("=== LOG ===");
  sections.push(divergence.proofPulseLog ?? "(no log available)");

  return sections.join("\n");
}

// --- Source truncation (2.5) ---

export function truncateSource(source: string, maxLines: number): string {
  const lines = source.split("\n");
  if (lines.length <= maxLines) return source;

  const specPattern = /\b(ensures|requires|invariant)\b/;
  const specLines: { idx: number; line: string }[] = [];
  const otherLines: { idx: number; line: string }[] = [];

  for (let i = 0; i < lines.length; i++) {
    if (specPattern.test(lines[i])) {
      specLines.push({ idx: i, line: lines[i] });
    } else {
      otherLines.push({ idx: i, line: lines[i] });
    }
  }

  // Always include spec lines first, fill remaining with other lines
  const budget = maxLines;
  const kept: { idx: number; line: string }[] = [];

  for (const sl of specLines) {
    if (kept.length >= budget) break;
    kept.push(sl);
  }

  for (const ol of otherLines) {
    if (kept.length >= budget) break;
    kept.push(ol);
  }

  // Sort by original index to preserve order
  kept.sort((a, b) => a.idx - b.idx);
  return kept.map((k) => k.line).join("\n");
}

// --- Divergence identification (2.6) ---

export function identifyDivergences(
  results: ClassificationResult[],
  oracleMap: Map<string, OracleEntry>,
): DivergenceInfo[] {
  const divergences: DivergenceInfo[] = [];

  for (const r of results) {
    if (r.classification === "error") continue;
    const oracle = oracleMap.get(r.taskId);
    if (!oracle) continue;

    const dataset = oracle.dataset;
    const source = oracle.dafnyCode;
    const coverageStatuses: Record<number, string> = {};
    for (const [k, v] of Object.entries(r.coverageStatuses)) {
      coverageStatuses[Number(k)] = String(v);
    }

    // Postcondition: strong/weak vs oracle postcondition label, skip oracle="wrong"
    if (oracle.labels.postcondition && oracle.labels.postcondition !== "wrong") {
      const pred = r.categories.postcondition === "strong";
      const actual = oracle.labels.postcondition === "strong";
      if (pred !== actual && r.categories.postcondition !== "none") {
        const direction: "FP" | "FN" = pred ? "FP" : "FN";
        divergences.push({
          dataset,
          taskId: r.taskId,
          category: "postcondition",
          direction,
          predicted: r.categories.postcondition,
          oracle: oracle.labels.postcondition,
          source,
          coverageStatuses,
          proofPulseLog: null,
        });
      }
    }

    // Precondition: required/optional vs oracle precondition label
    if (oracle.labels.precondition && r.categories.precondition !== "none") {
      const pred = r.categories.precondition === "required";
      const actual = oracle.labels.precondition === "required";
      if (pred !== actual) {
        const direction: "FP" | "FN" = pred ? "FP" : "FN";
        divergences.push({
          dataset,
          taskId: r.taskId,
          category: "precondition",
          direction,
          predicted: r.categories.precondition,
          oracle: oracle.labels.precondition,
          source,
          coverageStatuses,
          proofPulseLog: null,
        });
      }
    }

    // Invariant: strong/weak vs oracle invariant label
    if (oracle.labels.invariant && r.categories.invariant !== "none") {
      const pred = r.categories.invariant === "strong";
      const actual = oracle.labels.invariant === "strong";
      if (pred !== actual) {
        const direction: "FP" | "FN" = pred ? "FP" : "FN";
        divergences.push({
          dataset,
          taskId: r.taskId,
          category: "invariant",
          direction,
          predicted: r.categories.invariant,
          oracle: oracle.labels.invariant,
          source,
          coverageStatuses,
          proofPulseLog: null,
        });
      }
    }
  }

  return divergences;
}

// --- Report generation (2.7) ---

export function generateReport(classifications: AgentClassificationResult[]): string {
  const lines: string[] = [];
  lines.push("# Agent Divergence Classification Report");
  lines.push("");
  lines.push(`Total classifications: ${classifications.length}`);
  lines.push("");

  // Group by rootCause
  const groups = new Map<RootCause, AgentClassificationResult[]>();
  for (const c of classifications) {
    const list = groups.get(c.rootCause) ?? [];
    list.push(c);
    groups.set(c.rootCause, list);
  }

  // Sort groups by count descending
  const sorted = [...groups.entries()].sort((a, b) => b[1].length - a[1].length);

  for (const [cause, items] of sorted) {
    lines.push(`## ${cause} (${items.length})`);
    lines.push("");
    lines.push("| Dataset | Task | Category | Dir | Confidence | Oracle Error | File | Log |");
    lines.push("|---------|------|----------|-----|------------|--------------|------|-----|");
    for (const item of items) {
      const fileLink = `[${path.basename(item.relativePath)}](${item.relativePath})`;
      const logLink = item.logPath ? `[log](${item.logPath})` : "-";
      lines.push(
        `| ${item.dataset} | ${item.taskId} | ${item.category} | ${item.direction} | ${item.confidence.toFixed(2)} | ${item.oracleError} | ${fileLink} | ${logLink} |`,
      );
    }
    lines.push("");
    // Show explanations
    lines.push("<details><summary>Explanations</summary>");
    lines.push("");
    for (const item of items) {
      lines.push(`- **${item.dataset}/task_${item.taskId} (${item.category} ${item.direction})**: ${item.explanation}`);
    }
    lines.push("");
    lines.push("</details>");
    lines.push("");
  }

  return lines.join("\n");
}

// --- Summary generation (2.8) ---

export function generateSummary(classifications: AgentClassificationResult[]): string {
  const counts = new Map<RootCause, number>();
  for (const c of classifications) {
    counts.set(c.rootCause, (counts.get(c.rootCause) ?? 0) + 1);
  }

  const lines: string[] = [];
  lines.push("Root Cause                    | Count");
  lines.push("------------------------------|------");

  const sorted = [...counts.entries()].sort((a, b) => b[1] - a[1]);
  for (const [cause, count] of sorted) {
    lines.push(`${cause.padEnd(30)}| ${count}`);
  }

  lines.push(`${"TOTAL".padEnd(30)}| ${classifications.length}`);
  return lines.join("\n");
}
