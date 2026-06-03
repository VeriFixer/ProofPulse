#!/usr/bin/env node
/**
 * ProofPulse CLI — run coverage analysis on a Dafny file.
 *
 * Usage:
 *   npx proofpulse <file.dfy> [options]
 *
 * Options:
 *   --dafny-path <path>   Path to Dafny binary (default: "dafny")
 *   --minimize            Enable unsat core minimization
 *   --no-abstract-interpretation  Disable abstract interpretation
 *   --timeout <seconds>   Verification timeout (default: 60)
 *   --log                 Print YAML report (only uncovered/partial nodes)
 *   --log-verbose         Print full YAML report (all nodes + proof dependencies)
 *   -h, --help            Show help
 */
import * as fs from "node:fs";
import { runDafny } from "./dafny-runner.js";
import { parseProof } from "./proof.js";
import { generateTextReport } from "./report.js";

function printHelp() {
  console.log(`
ProofPulse — Dafny proof coverage analysis

Usage:
  npx proofpulse <file.dfy> [options]

Options:
  --dafny-path <path>   Path to Dafny binary (default: "dafny")
  --minimize            Enable unsat core minimization
  --no-abstract-interpretation  Disable abstract interpretation
  --timeout <seconds>   Verification timeout (default: 60)
  --log                 Print YAML report (only uncovered/partial nodes)
  --log-verbose         Print full YAML report (all nodes + proof dependencies)
  -h, --help            Show help
`.trim());
}

async function main() {
  const args = process.argv.slice(2);

  if (args.length === 0 || args.includes("-h") || args.includes("--help")) {
    printHelp();
    process.exit(0);
  }

  let filePath = "";
  let dafnyPath = "dafny";
  let minimize = false;
  let noAbstractInterpretation = false;
  let timeout = 60;
  let logMode: "none" | "default" | "verbose" = "none";

  for (let i = 0; i < args.length; i++) {
    switch (args[i]) {
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
        logMode = "default";
        break;
      case "--log-verbose":
        logMode = "verbose";
        break;
      default:
        if (!args[i].startsWith("-")) {
          filePath = args[i];
        }
    }
  }

  if (!filePath) {
    console.error("Error: no .dfy file specified");
    process.exit(1);
  }

  if (!fs.existsSync(filePath)) {
    console.error(`Error: file not found: ${filePath}`);
    process.exit(1);
  }

  const result = await runDafny(filePath, {
    dafnyPath,
    forceMinimization: minimize,
    noAbstractInterpretation,
    timeoutSeconds: timeout,
  });

  if (result.error) {
    console.error(`Dafny error: ${result.error}`);
    process.exit(1);
  }

  if (result.timedOut) {
    console.error("Dafny timed out");
    process.exit(1);
  }

  const sourceCode = fs.readFileSync(filePath, "utf-8");
  const proof = parseProof(sourceCode, result.log);

  // Default: always print the report (--log or --log-verbose just controls verbosity)
  // If neither flag given, print default (compact) report
  if (logMode === "none") {
    logMode = "default";
  }

  const report = generateTextReport(sourceCode, proof, { verbose: logMode === "verbose" });
  console.log(report);
}

main().catch((err) => {
  console.error(err.message ?? err);
  process.exit(1);
});
