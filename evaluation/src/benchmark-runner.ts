import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import {
  runDafny,
  parseProof,
  generateTextReport,
  type NodeData,
  TokenType,
  CovStatus,
} from "@proofpulse/core";
import { buildLogPath } from "./agent-helpers.js";
import { parseOracle, type DatasetId, type OracleEntry } from "./oracle-parser.js";
import {
  classifySpec,
  classifyAll,
  type ClassificationResult,
  type CategoryClassification,
} from "./classifier.js";
import {
  computeConfusionMatrix,
  computeMetrics,
  computeCategoryTables,
  formatTable,
  formatCategoryTables,
  type ConfusionMatrix,
  type Metrics,
} from "./reporter.js";

export interface ComparisonEntry {
  taskId: string;
  baselineClassification: string;
  minimizedClassification: string;
  changed: boolean;
  baselineDurationMs: number;
  minimizedDurationMs: number;
  baselineCategories?: CategoryClassification;
  minimizedCategories?: CategoryClassification;
}

export interface CategoryComparisonSummary {
  postconditionChanged: number;
  preconditionChanged: number;
  invariantChanged: number;
  total: number;
}

export interface TestComparisonEntry {
  srcFile: string;
  baselineStatus: string;
  minimizedStatus: string;
  changed: boolean;
}

export interface ComparisonResults {
  entries: ComparisonEntry[];
  changedResults: number;
  totalEntries: number;
  addedTimeMs: number;
  slowdownFactor: number;
  baselineTotalMs: number;
  minimizedTotalMs: number;
  testComparison: TestComparisonEntry[];
  testChangedCount: number;
}

export interface BenchmarkOptions {
  dafnyPath?: string;
  timeoutSeconds?: number;
  repoRoot: string;
  outputPath?: string;
  interactive?: boolean;
  verbose?: boolean;
  dataset?: DatasetId;
  concurrency?: number;
  forceMinimization?: boolean;
  compareMinimization?: boolean;
  noAbstractInterpretation?: boolean;
}

export interface BenchmarkResults {
  results: ClassificationResult[];
  confusionMatrix: ConfusionMatrix;
  metrics: Metrics;
  summary: { total: number; processed: number; errors: number; skipped: number };
}

function isInvariantNode(n: NodeData): boolean {
  return (n.prooftexts[0] ?? "").includes("loop invariant");
}

interface TimedClassificationResult extends ClassificationResult {
  durationMs: number;
}

async function processEntry(
  entry: OracleEntry,
  options: BenchmarkOptions,
): Promise<TimedClassificationResult> {
  const startMs = Date.now();
  let classification: "strong" | "weak" | "error";
  let categories: CategoryClassification = { postcondition: "none", precondition: "none", invariant: "none" };
  let postconditionLines: number[] = [];
  let preconditionLines: number[] = [];
  let invariantLines: number[] = [];
  let bodyLines: number[] = [];
  let coverageStatuses: Record<number, CovStatus> = {};
  let errorMsg: string | undefined;

  try {
    const dafnyResult = await runDafny(entry.filePath, {
      dafnyPath: options.dafnyPath,
      timeoutSeconds: options.timeoutSeconds,
      forceMinimization: options.forceMinimization,
      noAbstractInterpretation: options.noAbstractInterpretation,
    });

    if (dafnyResult.error || dafnyResult.timedOut) {
      classification = "error";
      errorMsg = dafnyResult.error ?? "timeout";
    } else {
      const sourceCode = fs.readFileSync(entry.filePath, "utf-8");
      const proof = parseProof(sourceCode, dafnyResult.log);
      const nodes = proof.proofGraph.getAllNodes();

      classification = classifySpec(proof.proofGraph);
      categories = classifyAll(proof.proofGraph, nodes as NodeData[]);

      postconditionLines = nodes
        .filter((n) => n.type === TokenType.Postcondition)
        .map((n) => n.start.line);
      preconditionLines = nodes
        .filter((n) => n.type === TokenType.Precondition)
        .map((n) => n.start.line);
      invariantLines = nodes
        .filter((n) => isInvariantNode(n))
        .map((n) => n.start.line);
      bodyLines = nodes
        .filter((n) => n.type === TokenType.CodeLine && !isInvariantNode(n))
        .map((n) => n.start.line);
      for (const n of nodes) {
        const line = n.start.line;
        const existing = coverageStatuses[line];
        if (existing === undefined) {
          coverageStatuses[line] = n.covStatus;
        } else if (existing === CovStatus.CovComplete && n.covStatus !== CovStatus.CovComplete) {
          coverageStatuses[line] = n.covStatus;
        } else if (existing === CovStatus.CovTest && n.covStatus === CovStatus.Uncovered) {
          coverageStatuses[line] = n.covStatus;
        }
      }

      // Write ProofPulse text report to log store
      try {
        const report = generateTextReport(sourceCode, proof);
        const logFilePath = buildLogPath(entry.dataset, path.basename(entry.filePath));
        fs.mkdirSync(path.dirname(logFilePath), { recursive: true });
        fs.writeFileSync(logFilePath, report);
      } catch {
        // Log write failure — continue silently
      }
    }
  } catch (err) {
    classification = "error";
    errorMsg = (err as Error).message;
  }

  const durationMs = Date.now() - startMs;
  return {
    taskId: entry.taskId,
    filePath: entry.filePath,
    classification,
    categories,
    oracleLabel: entry.label,
    postconditionLines,
    preconditionLines,
    invariantLines,
    bodyLines,
    coverageStatuses,
    durationMs,
    ...(errorMsg ? { error: errorMsg } : {}),
  };
}

export async function runBenchmark(
  options: BenchmarkOptions,
): Promise<BenchmarkResults> {
  const outputPath = options.outputPath ?? "benchmark-results.json";
  const entries = parseOracle(options.repoRoot, options.dataset);
  const total = entries.length;

  const useParallel = !options.verbose && !options.interactive;
  const concurrency = useParallel
    ? (options.concurrency ?? Math.max(1, os.cpus().length - 1))
    : 1;

  if (options.compareMinimization) {
    // Run baseline (no minimization)
    const baselineOpts = { ...options, forceMinimization: false, compareMinimization: false };
    const baselineResults = await runEntries(entries, baselineOpts, concurrency, "baseline");

    // Run minimized
    const minimizedOpts = { ...options, forceMinimization: true, compareMinimization: false };
    const minimizedResults = await runEntries(entries, minimizedOpts, concurrency, "minimized");

    // Build comparison entries
    const comparisonEntries: ComparisonEntry[] = baselineResults.map((b, i) => {
      const m = minimizedResults[i];
      return {
        taskId: b.taskId,
        baselineClassification: b.classification,
        minimizedClassification: m.classification,
        changed: b.classification !== m.classification,
        baselineDurationMs: b.durationMs,
        minimizedDurationMs: m.durationMs,
        baselineCategories: b.categories,
        minimizedCategories: m.categories,
      };
    });

    const changedResults = comparisonEntries.filter((e) => e.changed).length;
    const baselineTotalMs = comparisonEntries.reduce((s, e) => s + e.baselineDurationMs, 0);
    const minimizedTotalMs = comparisonEntries.reduce((s, e) => s + e.minimizedDurationMs, 0);
    const addedTimeMs = minimizedTotalMs - baselineTotalMs;
    const slowdownFactor = baselineTotalMs === 0 ? 0 : minimizedTotalMs / baselineTotalMs;

    const comparisonResults: ComparisonResults = {
      entries: comparisonEntries,
      changedResults,
      totalEntries: comparisonEntries.length,
      addedTimeMs,
      slowdownFactor,
      baselineTotalMs,
      minimizedTotalMs,
      testComparison: [],
      testChangedCount: 0,
    };

    // Write comparison results to separate file
    const comparisonPath = outputPath.replace(/\.json$/, "-comparison.json");
    fs.writeFileSync(comparisonPath, JSON.stringify(comparisonResults, null, 2));
    console.log(`Comparison results written to ${comparisonPath}`);

    // Also write minimized results separately
    const minimizedOutputPath = outputPath.replace(/\.json$/, "-minimized.json");
    buildBenchmarkResults(minimizedResults, entries, minimizedOutputPath);

    // Return baseline results as the normal output
    return buildBenchmarkResults(baselineResults, entries, outputPath);
  }

  let results: TimedClassificationResult[];

  if (concurrency > 1) {
    console.log(`Running ${total} entries with concurrency=${concurrency}...`);
    results = await runParallel(entries, options, concurrency);
  } else {
    results = await runSequential(entries, options);
  }

  return buildBenchmarkResults(results, entries, outputPath);
}

export function computeComparisonMetrics(
  baselineClassifications: string[],
  minimizedClassifications: string[],
  baselineDurations: number[],
  minimizedDurations: number[],
): { changedResults: number; addedTimeMs: number; slowdownFactor: number; baselineTotalMs: number; minimizedTotalMs: number } {
  let changedResults = 0;
  for (let i = 0; i < baselineClassifications.length; i++) {
    if (baselineClassifications[i] !== minimizedClassifications[i]) changedResults++;
  }
  const baselineTotalMs = baselineDurations.reduce((s, d) => s + d, 0);
  const minimizedTotalMs = minimizedDurations.reduce((s, d) => s + d, 0);
  const addedTimeMs = minimizedTotalMs - baselineTotalMs;
  const slowdownFactor = baselineTotalMs === 0 ? 0 : minimizedTotalMs / baselineTotalMs;
  return { changedResults, addedTimeMs, slowdownFactor, baselineTotalMs, minimizedTotalMs };
}

export function computeCategoryComparisonSummary(entries: ComparisonEntry[]): CategoryComparisonSummary {
  let postconditionChanged = 0;
  let preconditionChanged = 0;
  let invariantChanged = 0;

  for (const e of entries) {
    if (!e.baselineCategories || !e.minimizedCategories) continue;
    if (e.baselineCategories.postcondition !== e.minimizedCategories.postcondition) postconditionChanged++;
    if (e.baselineCategories.precondition !== e.minimizedCategories.precondition) preconditionChanged++;
    if (e.baselineCategories.invariant !== e.minimizedCategories.invariant) invariantChanged++;
  }

  return { postconditionChanged, preconditionChanged, invariantChanged, total: entries.length };
}

function buildBenchmarkResults(
  results: TimedClassificationResult[],
  entries: OracleEntry[],
  outputPath: string,
): BenchmarkResults {
  const total = entries.length;
  const errors = results.filter((r) => r.classification === "error").length;
  const confusionMatrix = computeConfusionMatrix(results);
  const metrics = computeMetrics(confusionMatrix);
  const processed = results.filter((r) => r.classification !== "error").length;

  const catTables = computeCategoryTables(results, entries);
  console.log(formatCategoryTables(catTables));

  const benchmarkResults: BenchmarkResults = {
    results,
    confusionMatrix,
    metrics,
    summary: { total, processed, errors, skipped: total - results.length },
  };

  fs.writeFileSync(outputPath, JSON.stringify(benchmarkResults, null, 2));
  console.log(`Results written to ${outputPath}`);

  return benchmarkResults;
}

async function runEntries(
  entries: OracleEntry[],
  options: BenchmarkOptions,
  concurrency: number,
  label: string,
): Promise<TimedClassificationResult[]> {
  console.log(`Running ${entries.length} entries (${label})...`);
  if (concurrency > 1) {
    return runParallel(entries, options, concurrency);
  }
  return runSequential(entries, options);
}

async function runParallel(
  entries: OracleEntry[],
  options: BenchmarkOptions,
  concurrency: number,
): Promise<TimedClassificationResult[]> {
  const results: TimedClassificationResult[] = new Array(entries.length);
  let completed = 0;
  let idx = 0;

  async function worker() {
    while (true) {
      const i = idx++;
      if (i >= entries.length) break;
      results[i] = await processEntry(entries[i], options);
      completed++;
      process.stdout.write(`\r[${completed}/${entries.length}] completed`);
    }
  }

  const workers = Array.from({ length: Math.min(concurrency, entries.length) }, () => worker());
  await Promise.all(workers);
  console.log("");
  return results;
}

async function runSequential(
  entries: OracleEntry[],
  options: BenchmarkOptions,
): Promise<TimedClassificationResult[]> {
  const total = entries.length;
  const results: TimedClassificationResult[] = [];

  for (let i = 0; i < entries.length; i++) {
    const entry = entries[i];
    console.log(`[${i + 1}/${total}] Processing ${entry.filePath}...`);

    const result = await processEntry(entry, options);
    results.push(result);

    if (options.verbose) {
      console.log(`\n${"═".repeat(60)}`);
      console.log(`Task: ${entry.taskId} | File: ${entry.filePath}`);
      console.log(`${"─".repeat(60)}`);
      try { console.log(fs.readFileSync(entry.filePath, "utf-8")); } catch {}
      console.log(`${"─".repeat(60)}`);
      console.log(`Coverage post=${result.categories.postcondition} pre=${result.categories.precondition} inv=${result.categories.invariant}`);
      console.log(`Oracle   post=${entry.labels.postcondition ?? "-"} pre=${entry.labels.precondition ?? "-"} inv=${entry.labels.invariant ?? "-"}`);
      console.log(`Overall: coverage=${result.classification} oracle=${entry.label} ${result.classification === entry.label ? "PASS ✓" : "FAIL ✗"}`);
      if (result.error) console.log(`Error: ${result.error}`);
      console.log(`${"═".repeat(60)}\n`);
    }

    if (options.interactive) {
      try {
        const { printInteractiveStep } = await import("./interactive.js");
        await printInteractiveStep({
          filePath: entry.filePath,
          coverageJson: result.coverageStatuses,
          classification: result.classification,
          oracleLabel: entry.label,
          pass: result.classification === entry.label,
        });
      } catch {}
    }
  }

  return results;
}
