import * as fs from "node:fs";
import * as path from "node:path";
import { runBenchmark } from "./benchmark-runner.js";
import { formatTable } from "./reporter.js";
import type { DatasetId } from "./oracle-parser.js";

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
  }
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
