#!/usr/bin/env node
/**
 * ProofPulse CLI — run proof coverage analysis on a source file.
 *
 * Usage:
 *   npx proofpulse <file> [options]
 *
 * Options:
 *   --backend <id>        Verifier backend (default: from the file extension; available: dafny)
 *   --dafny-path <path>   Path to Dafny binary (default: "dafny")
 *   --minimize            Enable unsat core minimization
 *   --no-abstract-interpretation  Disable abstract interpretation
 *   --cores <n>           Solver processes Dafny runs in parallel (default: Dafny's, half the cores)
 *   --timeout <seconds>   Time limit for each proof goal (default: 60)
 *   --do-not-use-custom-wrapped-z3  Run z3 itself, without ProofPulse's wrapper (for timing)
 *   --no-trigger-trace    Do not trace facts that supplied trigger terms (for timing)
 *   --stream <path>       As each method is verified, append its findings to <path> ("-" = stdout)
 *   --total-timeout <seconds>  Time limit for the whole run (default: none); the methods finished by then are reported
 *   --report <path>       Analyze a saved coverage report instead of running the verifier
 *   --emit-report <path>  Write the coverage report of this run (.json → JSON, else YAML)
 *   --log                 Print YAML report (only uncovered/partial nodes)
 *   --log-verbose         Print full YAML report (all nodes + proof dependencies)
 *   --show-implicit       Also report implicit checks in the YAML report
 *   -h, --help            Show help
 */
import * as fs from "node:fs";
import { analyzeReport } from "./proof.js";
import { generateTextReport } from "./report.js";
import { createDefaultRegistry } from "./backends/registry.js";
import { BackendOptions, CoreCheckConfig, RunStatus } from "./backends/backend.js";
import { CoverageReport, VerifierId, enumValues } from "./report/coverage-report.js";
import { parseCoverageReport, reportFormatForPath, serializeCoverageReport } from "./report/io.js";
import { DEFAULT_DAFNY_COMMAND } from "./backends/dafny/runner.js";
import { assertNever } from "./util/assert-never.js";

/** How much of the text report to print. */
enum LogMode {
  None = "none",
  Default = "default",
  Verbose = "verbose",
}

const VERIFIER_IDS = enumValues(VerifierId);

function printHelp() {
  console.log(`
ProofPulse — proof coverage analysis

Usage:
  npx proofpulse <file> [options]

Options:
  --backend <id>        Verifier backend (default: from the file extension; available: dafny)
  --dafny-path <path>   Path to Dafny binary (default: "dafny")
  --minimize            Enable unsat core minimization
  --no-abstract-interpretation  Disable abstract interpretation
  --cores <n>           Solver processes Dafny runs in parallel (default: Dafny's, half the cores)
  --timeout <seconds>   Time limit for each proof goal (default: 60)
  --do-not-use-custom-wrapped-z3  Run z3 itself, without ProofPulse's wrapper: cores are not checked
                        (for timing; coverage may miss facts that only supplied trigger terms)
  --no-trigger-trace    Do not trace facts that supplied trigger terms (for timing)
  --stream <path>       As each method is verified, append its findings to <path> ("-" = stdout).
                        Statuses that depend on callers not yet verified may change in the final report.
  --total-timeout <seconds>  Time limit for the whole run (default: none); the methods finished by then are reported
  --report <path>       Analyze a saved coverage report (YAML/JSON) instead of running the verifier
  --emit-report <path>  Write the coverage report of this run (.json → JSON, otherwise YAML)
  --log                 Print YAML report (only uncovered/partial nodes)
  --log-verbose         Print full YAML report (all nodes + proof dependencies)
  --show-implicit       Also report implicit checks (null, index range, ...) in the YAML report
  --generate-yaml <path>  Write full YAML to file (can be combined with --log-verbose)
  -h, --help            Show help
`.trim());
}

function fail(message: string): never {
  console.error(message);
  process.exit(1);
}

async function main() {
  const args = process.argv.slice(2);

  if (args.length === 0 || args.includes("-h") || args.includes("--help")) {
    printHelp();
    process.exit(0);
  }

  let filePath = "";
  let backendId: VerifierId | undefined;
  let dafnyPath = DEFAULT_DAFNY_COMMAND;
  let minimize = false;
  let noAbstractInterpretation = false;
  let cores: number | undefined;
  let timeout = 60;
  let totalTimeout: number | undefined;
  let streamPath: string | null = null;
  const coreCheck: CoreCheckConfig = {};
  let logMode = LogMode.None;
  let showImplicit = false;
  let generateYamlPath: string | null = null;
  let reportPath: string | null = null;
  let emitReportPath: string | null = null;

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
      case "--backend": {
        const id = args[++i];
        if (!VERIFIER_IDS.has(id)) fail(`Error: unknown backend "${id}"`);
        backendId = id as VerifierId;
        break;
      }
      case "--dafny-path":
        dafnyPath = args[++i];
        break;
      case "--minimize":
        minimize = true;
        break;
      case "--no-abstract-interpretation":
        noAbstractInterpretation = true;
        break;
      case "--cores":
        cores = parseInt(args[++i], 10);
        if (!(cores >= 1)) fail("Error: --cores needs a positive number");
        break;
      case "--timeout":
        timeout = parseInt(args[++i], 10);
        break;
      case "--do-not-use-custom-wrapped-z3":
        coreCheck.useWrapper = false;
        break;
      case "--no-trigger-trace":
        coreCheck.triggerTrace = false;
        break;
      case "--stream":
        streamPath = args[++i];
        break;
      case "--total-timeout":
        totalTimeout = parseInt(args[++i], 10);
        if (!(totalTimeout >= 1)) fail("Error: --total-timeout needs a positive number");
        break;
      case "--log":
        logMode = LogMode.Default;
        break;
      case "--log-verbose":
        logMode = LogMode.Verbose;
        break;
      case "--show-implicit":
        showImplicit = true;
        break;
      case "--generate-yaml":
        generateYamlPath = args[++i];
        break;
      case "--report":
        reportPath = args[++i];
        break;
      case "--emit-report":
        emitReportPath = args[++i];
        break;
      default:
        if (!args[i].startsWith("-")) {
          filePath = args[i];
        }
    }
  }

  if (!filePath) fail("Error: no source file specified");
  if (!fs.existsSync(filePath)) fail(`Error: file not found: ${filePath}`);

  let report: CoverageReport;
  if (reportPath) {
    try {
      report = parseCoverageReport(fs.readFileSync(reportPath, "utf-8"));
    } catch (err) {
      fail(`Error reading coverage report ${reportPath}: ${(err as Error).message}`);
    }
  } else {
    const registry = createDefaultRegistry();
    const backend = backendId ? registry.get(backendId) : registry.backendForFile(filePath);
    if (!backend) {
      fail(backendId
        ? `Error: backend "${backendId}" is not available`
        : `Error: no backend handles ${filePath} (supported: ${registry.fileExtensions().join(", ")})`);
    }

    const options: BackendOptions = {
      toolPath: dafnyPath,
      timeoutSeconds: timeout,
      ...(totalTimeout !== undefined ? { totalTimeoutSeconds: totalTimeout } : {}),
      ...(Object.keys(coreCheck).length > 0 ? { coreCheck } : {}),
      ...(minimize ? { minimization: {} } : {}),
      ...(backend.id === VerifierId.Dafny
        ? { backendOptions: { backend: VerifierId.Dafny, noAbstractInterpretation, cores } }
        : {}),
    };
    // Name each method on stderr as it finishes, so long runs show progress,
    // and with --stream write its findings out as well.
    const source = streamPath ? fs.readFileSync(filePath, "utf-8") : "";
    if (streamPath && streamPath !== "-") fs.writeFileSync(streamPath, "");
    const finished = new Set<string>();
    const run = await backend.run(filePath, {
      ...options,
      onPartialResult: (partial) => {
        if (!partial.report) return;
        const fresh = new Set(partial.report.units.map((u) => u.name).filter((name) => !finished.has(name)));
        for (const name of fresh) {
          finished.add(name);
          console.error(`[${finished.size}] verified ${name}`);
        }
        if (streamPath && fresh.size > 0) {
          const units = { ...partial.report, units: partial.report.units.filter((u) => fresh.has(u.name)) };
          const findings = generateTextReport(source, analyzeReport(source, units), { includeImplicit: showImplicit });
          const text = `${[...fresh].map((name) => `# verified ${name}`).join("\n")}\n${findings}\n`;
          if (streamPath === "-") process.stdout.write(text);
          else fs.appendFileSync(streamPath, text);
        }
      },
    });

    switch (run.status) {
      case RunStatus.Completed:
        break;
      case RunStatus.TimedOut:
        if (!run.report) fail(`${backend.displayName} timed out`);
        console.error(`${backend.displayName} timed out; reporting the ${new Set(run.report.units.map((u) => u.name)).size} methods that finished`);
        break;
      case RunStatus.Aborted:
        fail(`${backend.displayName} run aborted`);
      case RunStatus.Failed:
        fail(`${backend.displayName} error: ${run.errorMessage}`);
      default:
        assertNever(run.status, "run status");
    }
    report = run.report!;
  }

  if (emitReportPath) {
    try {
      fs.writeFileSync(emitReportPath, serializeCoverageReport(report, reportFormatForPath(emitReportPath)));
    } catch (err) {
      fail(`Error writing coverage report to ${emitReportPath}: ${(err as Error).message}`);
    }
  }

  const sourceCode = fs.readFileSync(filePath, "utf-8");
  const proof = analyzeReport(sourceCode, report);

  if (generateYamlPath) {
    try {
      fs.writeFileSync(generateYamlPath, proof.proofGraph.toYAML());
    } catch (err) {
      fail(`Error writing YAML to ${generateYamlPath}: ${(err as Error).message}`);
    }
  }

  // Default: always print the report (--log or --log-verbose just controls verbosity)
  // If neither flag given, print default (compact) report
  if (logMode === LogMode.None) {
    logMode = LogMode.Default;
  }

  const textReport = generateTextReport(sourceCode, proof, { verbose: logMode === LogMode.Verbose, includeImplicit: showImplicit });
  console.log(textReport);
}

main().catch((err) => {
  console.error(err.message ?? err);
  process.exit(1);
});
