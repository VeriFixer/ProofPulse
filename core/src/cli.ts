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
 *   --timeout <seconds>   Verification timeout (default: 60)
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
import { BackendOptions, RunStatus } from "./backends/backend.js";
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
  --timeout <seconds>   Verification timeout (default: 60)
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
  let timeout = 60;
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
      case "--timeout":
        timeout = parseInt(args[++i], 10);
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
      ...(minimize ? { minimization: {} } : {}),
      ...(backend.id === VerifierId.Dafny
        ? { backendOptions: { backend: VerifierId.Dafny, noAbstractInterpretation } }
        : {}),
    };
    const run = await backend.run(filePath, options);

    switch (run.status) {
      case RunStatus.Completed:
        break;
      case RunStatus.TimedOut:
        fail(`${backend.displayName} timed out`);
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
