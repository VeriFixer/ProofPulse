import * as fs from "node:fs";
import * as os from "node:os";
import {
  runDafny,
  parseProof,
  type NodeData,
  TokenType,
  CovStatus,
} from "@proofpulse/core";
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

export interface BenchmarkOptions {
  dafnyPath?: string;
  timeoutSeconds?: number;
  repoRoot: string;
  outputPath?: string;
  interactive?: boolean;
  verbose?: boolean;
  dataset?: DatasetId;
  concurrency?: number;
}

export interface BenchmarkResults {
  results: ClassificationResult[];
  confusionMatrix: ConfusionMatrix;
  metrics: Metrics;
  summary: { total: number; processed: number; errors: number; skipped: number };
}

function isInvariantNode(n: NodeData): boolean {
  return n.prooftext.includes("loop invariant");
}

async function processEntry(
  entry: OracleEntry,
  options: BenchmarkOptions,
): Promise<ClassificationResult> {
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
    });

    if (dafnyResult.error || dafnyResult.timedOut) {
      classification = "error";
      errorMsg = dafnyResult.error ?? "timeout";
    } else {
      const sourceCode = fs.readFileSync(entry.filePath, "utf-8");
      const proof = parseProof(sourceCode, dafnyResult.log);
      const nodes = proof.proofGraph.getAllNodes();

      classification = classifySpec(nodes as NodeData[]);
      categories = classifyAll(nodes as NodeData[]);

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
        coverageStatuses[n.start.line] = n.covStatus;
      }
    }
  } catch (err) {
    classification = "error";
    errorMsg = (err as Error).message;
  }

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

  let results: ClassificationResult[];

  if (concurrency > 1) {
    console.log(`Running ${total} entries with concurrency=${concurrency}...`);
    results = await runParallel(entries, options, concurrency);
  } else {
    results = await runSequential(entries, options);
  }

  const errors = results.filter((r) => r.classification === "error").length;
  const confusionMatrix = computeConfusionMatrix(results);
  const metrics = computeMetrics(confusionMatrix);
  const processed = results.filter((r) => r.classification !== "error").length;

  // Print per-category tables
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

async function runParallel(
  entries: OracleEntry[],
  options: BenchmarkOptions,
  concurrency: number,
): Promise<ClassificationResult[]> {
  const results: ClassificationResult[] = new Array(entries.length);
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
): Promise<ClassificationResult[]> {
  const total = entries.length;
  const results: ClassificationResult[] = [];

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
