import * as fs from "node:fs";
import * as path from "node:path";
import { runBenchmark } from "./benchmark-runner.js";
import { formatTable, computeCategoryTables, generateAggregateLatexTables, type AggregatedDatasetMetrics } from "./reporter.js";
import { parseOracle, type DatasetId } from "./oracle-parser.js";

interface CliArgs {
  repoRoot: string;
  dafnyPath: string;
  timeout: number;
  output: string;
  interactive: boolean;
  verbose: boolean;
  dataset: DatasetId | "all";
  concurrency?: number;
  forceMinimization: boolean;
  compareMinimization: boolean;
}

function parseArgs(argv: string[]): CliArgs {
  const args = argv.slice(2);
  const opts: CliArgs = {
    repoRoot: "dafny-synthesis",
    dafnyPath: "dafny",
    timeout: 60,
    output: "evaluation/results/benchmark-results.json",
    interactive: false,
    verbose: false,
    dataset: "RQ3-GPT4",
    forceMinimization: false,
    compareMinimization: false,
  };

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case "--repo-root":
        opts.repoRoot = args[++i];
        break;
      case "--dafny-path":
        opts.dafnyPath = args[++i];
        break;
      case "--timeout":
        opts.timeout = parseInt(args[++i], 10);
        break;
      case "--output":
        opts.output = args[++i];
        break;
      case "--interactive":
        opts.interactive = true;
        break;
      case "--verbose":
        opts.verbose = true;
        break;
      case "--dataset":
        opts.dataset = args[++i] as DatasetId | "all";
        break;
      case "--concurrency":
        opts.concurrency = parseInt(args[++i], 10);
        break;
      case "--force-core-minimization":
        opts.forceMinimization = true;
        break;
      case "--compare-minimization":
        opts.compareMinimization = true;
        break;
    }
  }
  return opts;
}

async function main() {
  const opts = parseArgs(process.argv);

  const repoRoot = path.resolve(opts.repoRoot);
  if (!fs.existsSync(repoRoot)) {
    console.error(
      `dafny-synthesis submodule not found at ${repoRoot}. Run \`git submodule update --init\``
    );
    process.exit(1);
  }

  const { execSync } = await import("node:child_process");
  try {
    execSync(`${opts.dafnyPath} --version`, { stdio: "pipe" });
  } catch {
    console.error(`Dafny not found at ${opts.dafnyPath}`);
    process.exit(1);
  }

  const { ALL_DATASETS } = await import("./oracle-parser.js");
  const datasets: DatasetId[] = opts.dataset === "all"
    ? ALL_DATASETS.map((d) => d.id)
    : [opts.dataset as DatasetId];

  const allAggregatedMetrics: AggregatedDatasetMetrics[] = [];

  for (const dsId of datasets) {
    console.log(`\n${"═".repeat(60)}`);
    console.log(`Running benchmark: ${dsId}`);
    console.log(`${"═".repeat(60)}`);

    const outputFile = datasets.length > 1
      ? opts.output.replace(".json", `-${dsId}.json`)
      : opts.output;

    const outputDir = path.dirname(outputFile);
    if (!fs.existsSync(outputDir)) {
      fs.mkdirSync(outputDir, { recursive: true });
    }

    const results = await runBenchmark({
      repoRoot,
      dafnyPath: opts.dafnyPath,
      timeoutSeconds: opts.timeout,
      outputPath: outputFile,
      interactive: opts.interactive,
      verbose: opts.verbose,
      dataset: dsId,
      concurrency: opts.concurrency,
      forceMinimization: opts.forceMinimization,
      compareMinimization: opts.compareMinimization,
    });

    const table = formatTable(results.confusionMatrix, results.metrics, results.results);
    console.log("\n" + table);
    console.log(
      `\nSummary: ${results.summary.processed} processed, ${results.summary.errors} errors, ${results.summary.skipped} skipped out of ${results.summary.total} total`
    );

    // Collect metrics for aggregation when running all datasets
    if (datasets.length > 1) {
      const entries = parseOracle(repoRoot, dsId);
      const catTables = computeCategoryTables(results.results, entries);

      // Extract metrics from category tables
      const postTable = catTables[0]; // Postconditions
      const preTable = catTables[1];  // Preconditions
      const invTable = catTables[2];  // Invariants

      const aggregated: AggregatedDatasetMetrics = {
        datasetId: dsId,
        postconditions: {
          n: postTable.total,
          tp: postTable.confusionMatrix?.tp ?? 0,
          fp: postTable.confusionMatrix?.fp ?? 0,
          fn: postTable.confusionMatrix?.fn ?? 0,
          tn: postTable.confusionMatrix?.tn ?? 0,
          precision: postTable.metrics?.precision ?? 0,
          recall: postTable.metrics?.recall ?? 0,
          f1: postTable.metrics?.f1 ?? 0,
          accuracy: postTable.metrics?.accuracy ?? 0,
        },
        preconditions: {
          n: preTable.total,
          tp: preTable.confusionMatrix?.tp ?? 0,
          fp: preTable.confusionMatrix?.fp ?? 0,
          fn: preTable.confusionMatrix?.fn ?? 0,
          tn: preTable.confusionMatrix?.tn ?? 0,
          precision: preTable.metrics?.precision ?? 0,
          recall: preTable.metrics?.recall ?? 0,
          f1: preTable.metrics?.f1 ?? 0,
          accuracy: preTable.metrics?.accuracy ?? 0,
        },
        invariants: {
          n: invTable.total,
          tp: invTable.confusionMatrix?.tp ?? 0,
          fp: invTable.confusionMatrix?.fp ?? 0,
          fn: invTable.confusionMatrix?.fn ?? 0,
          tn: invTable.confusionMatrix?.tn ?? 0,
          precision: invTable.metrics?.precision ?? 0,
          recall: invTable.metrics?.recall ?? 0,
          f1: invTable.metrics?.f1 ?? 0,
          accuracy: invTable.metrics?.accuracy ?? 0,
        },
      };

      allAggregatedMetrics.push(aggregated);
    }
  }

  // Generate aggregate LaTeX tables if running all datasets
  if (datasets.length > 1 && allAggregatedMetrics.length > 0) {
    console.log(`\n${"═".repeat(60)}`);
    console.log("Generating Aggregate LaTeX Tables");
    console.log(`${"═".repeat(60)}`);

    const latexTables = generateAggregateLatexTables(allAggregatedMetrics);
    const latexFile = opts.output.replace(".json", "-aggregate-tables.tex");
    fs.writeFileSync(latexFile, latexTables);
    console.log(`\nAggregate LaTeX tables written to ${latexFile}`);
    console.log("\nYou can include these tables in your paper using:");
    console.log(`\\input{${path.relative(".", latexFile)}}`);
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
