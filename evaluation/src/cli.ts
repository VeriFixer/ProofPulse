import * as fs from "node:fs";
import * as path from "node:path";
import { runBenchmark, computeCategoryComparisonSummary, type ComparisonResults } from "./benchmark-runner.js";
import { formatTable, computeCategoryTables, generateAggregateLatexTables, generateComparisonAggregateLatexTable, type AggregatedDatasetMetrics, type ComparisonAggregateDatum } from "./reporter.js";
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

function printHelp(): void {
  console.log(`
Usage: npx tsx evaluation/src/cli.ts [options]

Options:
  -h, --help                    Show this help message
  --repo-root <path>            Path to dafny-synthesis repo (default: "dafny-synthesis")
  --dafny-path <path>           Dafny binary path (default: "dafny")
  --timeout <seconds>           Per-file verification timeout (default: 60)
  --output <path>               JSON results output (default: "evaluation/results/benchmark-results.json")
  --interactive                 Enable interactive mode
  --verbose                     Print per-file details (forces sequential)
  --dataset <id>                Dataset: RQ1-GPT4, RQ1-PaLM2, RQ2-GPT4, RQ2-PaLM2, RQ3-GPT4, RQ3-PaLM2, or "all" (default: "RQ3-GPT4")
  --concurrency <n>             Parallel Dafny workers (default: cpus-1)
  --force-core-minimization     Enable unsat core minimization
  --compare-minimization        Run twice (baseline vs minimized), report diffs
`.trim());
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
      case "-h":
      case "--help":
        printHelp();
        process.exit(0);
        break;
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

  // Run test suite once if compare-minimization is active
  if (opts.compareMinimization) {
    try {
      const { runAllTests } = await import("../../tests/harness/test_logic.js");
      console.log(`\n${"═".repeat(60)}`);
      console.log("Running test suite (with minimization) — single run");
      console.log(`${"═".repeat(60)}`);
      await runAllTests({ forceMinimization: true });
    } catch (err) {
      console.warn(`Test suite skipped: ${(err as Error).message}`);
    }
  }

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

  // Generate comparison aggregate table if compare-minimization + multiple datasets
  if (opts.compareMinimization && datasets.length > 1) {
    const comparisonData: ComparisonAggregateDatum[] = [];

    for (const dsId of datasets) {
      const compFile = opts.output.replace(".json", `-${dsId}-comparison.json`);
      if (!fs.existsSync(compFile)) continue;
      const comp: ComparisonResults = JSON.parse(fs.readFileSync(compFile, "utf-8"));
      const catSummary = computeCategoryComparisonSummary(comp.entries);
      comparisonData.push({
        datasetId: dsId,
        total: comp.totalEntries,
        overallChanged: comp.changedResults,
        postconditionChanged: catSummary.postconditionChanged,
        preconditionChanged: catSummary.preconditionChanged,
        invariantChanged: catSummary.invariantChanged,
      });
    }

    if (comparisonData.length > 0) {
      console.log(`\n${"═".repeat(60)}`);
      console.log("Minimization Comparison Aggregate");
      console.log(`${"═".repeat(60)}`);

      // Print console summary
      console.log("\n  Dataset              | N    | Overall | Post. | Pre. | Inv.");
      console.log("  " + "─".repeat(65));
      let tN = 0, tO = 0, tP = 0, tPre = 0, tI = 0;
      for (const d of comparisonData) {
        console.log(`  ${d.datasetId.padEnd(20)} | ${String(d.total).padStart(4)} | ${String(d.overallChanged).padStart(7)} | ${String(d.postconditionChanged).padStart(5)} | ${String(d.preconditionChanged).padStart(4)} | ${String(d.invariantChanged).padStart(4)}`);
        tN += d.total; tO += d.overallChanged; tP += d.postconditionChanged; tPre += d.preconditionChanged; tI += d.invariantChanged;
      }
      console.log("  " + "─".repeat(65));
      console.log(`  ${"Combined".padEnd(20)} | ${String(tN).padStart(4)} | ${String(tO).padStart(7)} | ${String(tP).padStart(5)} | ${String(tPre).padStart(4)} | ${String(tI).padStart(4)}`);

      // Write LaTeX table
      const compLatex = generateComparisonAggregateLatexTable(comparisonData);
      const compLatexFile = opts.output.replace(".json", "-comparison-aggregate.tex");
      fs.writeFileSync(compLatexFile, compLatex);
      console.log(`\nComparison LaTeX table written to ${compLatexFile}`);
    }

    // Generate separate aggregate LaTeX for minimized results
    const minimizedAggregated: AggregatedDatasetMetrics[] = [];
    for (const dsId of datasets) {
      const minFile = opts.output.replace(".json", `-${dsId}-minimized.json`);
      if (!fs.existsSync(minFile)) continue;
      const minData = JSON.parse(fs.readFileSync(minFile, "utf-8"));
      const entries = parseOracle(repoRoot, dsId);
      const catTables = computeCategoryTables(minData.results, entries);
      const postTable = catTables[0];
      const preTable = catTables[1];
      const invTable = catTables[2];
      minimizedAggregated.push({
        datasetId: dsId,
        postconditions: {
          n: postTable.total, tp: postTable.confusionMatrix?.tp ?? 0, fp: postTable.confusionMatrix?.fp ?? 0,
          fn: postTable.confusionMatrix?.fn ?? 0, tn: postTable.confusionMatrix?.tn ?? 0,
          precision: postTable.metrics?.precision ?? 0, recall: postTable.metrics?.recall ?? 0,
          f1: postTable.metrics?.f1 ?? 0, accuracy: postTable.metrics?.accuracy ?? 0,
        },
        preconditions: {
          n: preTable.total, tp: preTable.confusionMatrix?.tp ?? 0, fp: preTable.confusionMatrix?.fp ?? 0,
          fn: preTable.confusionMatrix?.fn ?? 0, tn: preTable.confusionMatrix?.tn ?? 0,
          precision: preTable.metrics?.precision ?? 0, recall: preTable.metrics?.recall ?? 0,
          f1: preTable.metrics?.f1 ?? 0, accuracy: preTable.metrics?.accuracy ?? 0,
        },
        invariants: {
          n: invTable.total, tp: invTable.confusionMatrix?.tp ?? 0, fp: invTable.confusionMatrix?.fp ?? 0,
          fn: invTable.confusionMatrix?.fn ?? 0, tn: invTable.confusionMatrix?.tn ?? 0,
          precision: invTable.metrics?.precision ?? 0, recall: invTable.metrics?.recall ?? 0,
          f1: invTable.metrics?.f1 ?? 0, accuracy: invTable.metrics?.accuracy ?? 0,
        },
      });
    }

    if (minimizedAggregated.length > 0) {
      console.log(`\n${"═".repeat(60)}`);
      console.log("Generating Minimized Aggregate LaTeX Tables");
      console.log(`${"═".repeat(60)}`);

      const minLatex = generateAggregateLatexTables(minimizedAggregated);
      const minLatexFile = opts.output.replace(".json", "-minimized-aggregate-tables.tex");
      fs.writeFileSync(minLatexFile, minLatex);
      console.log(`\nMinimized aggregate LaTeX written to ${minLatexFile}`);
    }
  }

  // Print minimization status
  console.log(`\nMinimization: ${opts.forceMinimization ? "ENABLED (--force-core-minimization)" : "DISABLED"}`);
  console.log(`Compare minimization: ${opts.compareMinimization ? "ENABLED (--compare-minimization)" : "DISABLED"}`);

  // Print output locations
  console.log(`\n${"─".repeat(60)}`);
  console.log("Output files:");
  if (datasets.length > 1) {
    for (const dsId of datasets) {
      const f = opts.output.replace(".json", `-${dsId}.json`);
      console.log(`  Results:    ${path.resolve(f)}`);
      if (opts.compareMinimization) {
        console.log(`  Comparison: ${path.resolve(f.replace(/\.json$/, "-comparison.json"))}`);
      }
    }
    const latexFile = opts.output.replace(".json", "-aggregate-tables.tex");
    console.log(`  LaTeX:      ${path.resolve(latexFile)}`);
    if (opts.compareMinimization) {
      const compLatexFile = opts.output.replace(".json", "-comparison-aggregate.tex");
      console.log(`  Comp. LaTeX: ${path.resolve(compLatexFile)}`);
    }
  } else {
    console.log(`  Results:    ${path.resolve(opts.output)}`);
    if (opts.compareMinimization) {
      console.log(`  Comparison: ${path.resolve(opts.output.replace(/\.json$/, "-comparison.json"))}`);
    }
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
