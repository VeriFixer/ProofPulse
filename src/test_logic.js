import { createRequire } from 'module';

const require = createRequire(import.meta.url);

const os = require("os");
const path = require("path");
const fs = require('fs');
import { writeFile } from "fs/promises";
const { spawn } = require("child_process");
const fsp = fs.promises;

import { parseProof } from '@proofpulse/core';
const DAFNY_TIMEOUT_SEC = parseInt(process.env.DAFNY_TIMEOUT_SEC, 10) || 60;

const CONCURRENCY = process.env.CI
  ? Math.max(1, os.cpus().length - 1)
  : os.cpus().length - 1;

const DEFAULT_TESTS_ROOT = path.join("dataset", "tests");

function parse_test(testSource) {
    var expected_lines = new Map();
    var test_name = ""
    var test_description

    const lineRegex = /^\/\/:::\s*L(\d+)\s*-\s*([A-Za-z.]+)/;
    const NameRegex = /^\/\/:::\s*Name\s*-\s*(.*)/;
    
    const lines = testSource.split(/\r?\n/);
    for (let i = 0; i < lines.length; i++) {
        const raw = lines[i];
        var lineN = -1;

        const lineMatch = raw.match(lineRegex);
        const nameMatch = raw.match(NameRegex);

        if (lineMatch) {
            expected_lines.set(lineMatch[1], lineMatch[2]);
        }

        if (nameMatch) {
            test_name = nameMatch[1];
        }
    }
    return [test_name, expected_lines];
}

function check_test(name, expected, received) {
    var test_passed = true;
    var reason = "\n"
    if(expected.size < 1){
       reason = `  Failed ${name} : expect comments are empty"`;
       test_passed = false;
    }
    for (const [lineNum, expectedStatus] of expected.entries()) {
        if (lineNum < 1 || lineNum > received.length) {
            test_passed = false;
            reason += `  Failed ${name} failed: Line ${lineNum} is out of bounds (received has ${received.length} lines).\n`;
        }

        const actualStatus = received[lineNum - 1];

        if (actualStatus !== expectedStatus) {
            test_passed = false;
            reason += `  Failed ${name}: Line ${lineNum} expected '${expectedStatus}', but got '${actualStatus}'.\n`;
        }
    }
    if(test_passed){
        reason += `  Passed ${name}`
    }
    return [test_passed, reason];
}

function findDfyFiles(startDir) {
  const out = [];

  function walk(dir) {
    const items = fs.readdirSync(dir, { withFileTypes: true });
    for (const it of items) {
      const full = path.join(dir, it.name);
      if (it.isDirectory()) {
        walk(full);
      } else if (it.isFile() && full.toLowerCase().endsWith(".dfy")) {
        out.push(full);
      }
    }
  }
  walk(startDir);
  return out;
}

async function runDafnyAndAppendLog(srcFilePath) {
  const dir = path.dirname(srcFilePath);
  const fileName = path.basename(srcFilePath);
  const proverLogPath = path.join(dir, "prover_log.txt");

  // Dafny arguments as requested
  const args = [
    "verify",
    fileName,
    "--verification-coverage-report", "cov",
    "--log-format", "text",
    "--solver-option", "LOG_FILE=output.smt2",
    "--bprint", "output.bpl",
    "--isolate-assertions",
    "--allow-warnings", "true",
    "--verification-time-limit", DAFNY_TIMEOUT_SEC,
    // Options to perform core minimization note: This does not gurantee that the core is really the minimal possible
    // Need also to pass produce proof to make proof more stable
    "--boogie", "/proverOpt:O:smt.core.minimize=true /proverOpt:O:sat.core.minimize=true  /proverOpt:C:proof=true" 
  ];
 const child = spawn("dafny", args, { cwd: dir });

  let stdout = "", stderr = "";

  child.stdout?.on("data", (b) => { stdout += b.toString(); });
  child.stderr?.on("data", (b) => { stderr += b.toString(); });

  const timeoutMs = DAFNY_TIMEOUT_SEC * 1000;
  const exit = await new Promise((resolve) => {
    let timedOut = false;
    const timer = setTimeout(() => {
      timedOut = true;
      child.kill('SIGKILL');
    }, timeoutMs);
    child.on("error", (err) => { clearTimeout(timer); resolve({ error: err }); });
    child.on("close", (code) => { clearTimeout(timer); resolve(timedOut ? { timedOut: true } : { code }); });
  });

  if (exit.timedOut) {
    return { ok: false, reason: "timeout" };
  }

  const header = `\n===== dafny run for ${fileName} (${new Date().toISOString()}) =====\n`;
  const footer = `\n===== end dafny run for ${fileName} =====\n`;
  const logContent = header + (stdout || "") + (stderr || "") + footer;

  try {
    await  writeFile(proverLogPath, logContent, { encoding: "utf8"});
  } catch (writeErr) {
    console.error(writeErr)
    return { ok: false, reason: "append_failed", writeErr };
  }

  if (exit.error) return { ok: false, reason: "spawn_error", error: exit.error, logPath: proverLogPath };

  return {
    ok: true,
    code: exit.code,
    stdout,
    stderr,
    logPath: proverLogPath,
    note: exit.code !== 0 ? "nonzero_exit" : undefined
  };
}
  

async function runTest(srcFile) {
  const dir = path.dirname(srcFile);
  const proofFile = path.join(dir, "prover_log.txt");

  // Remove existing prover_log.txt if present

  try {
    await fsp.unlink(proofFile).catch((e) => {
      if (e.code !== "ENOENT") throw e;
    });
  } catch (err) {
    return { srcFile, status: "error", reason: "unlink_failed", error: err };
  }

  // Run Dafny and create prover_log.txt by appending output
  const dafnyRes = await runDafnyAndAppendLog(srcFile);
  if (!dafnyRes.ok) {
    if (dafnyRes.reason === "timeout") {
      return { srcFile, status: "failed", reason: "timeout" };
    }
    return { srcFile, status: "skipped", reason: "dafny_failed", dafnyRes };
  }

  // Read source and log
  let src, log;
  try {
    src = await fsp.readFile(srcFile, "utf8");
  } catch (err) {
    return { srcFile, status: "error", reason: "read_source_failed", error: err };
  }
  try {
    log = await fsp.readFile(proofFile, "utf8");
  } catch (err) {
    return { srcFile, status: "error", reason: "read_log_failed", error: err };
  }

  // parseProof & parse_test (assumed to be synchronous functions available in scope)
  let proofTest, parsedTest;
  //try {
    proofTest = parseProof(src, log);
  //} catch (err) {
  //  return { srcFile, status: "error", reason: "parse_proof_failed", error: err };
  //}
  try {
    parsedTest = parse_test(src);
  } catch (err) {
    return { srcFile, status: "error", reason: "parse_test_failed", error: err };
  } 

  if (!Array.isArray(parsedTest) || parsedTest.length < 2) {
    return { srcFile, status: "error", reason: "parse_test_return_invalid", parsedTest };
  }

  const [test_name, testExpectedOut] = parsedTest;
  if (!(testExpectedOut instanceof Map)) {
    return { srcFile, status: "error", reason: "expected_not_map", expected: testExpectedOut };
  }

  const lineStatus = (proofTest && proofTest.lineStatus) || [];
  try {
    const  [ok, reason] = check_test(test_name, testExpectedOut, lineStatus);
    return { srcFile, status: ok ? "passed" : "failed", test_name, reason, lineStatus };
  } catch (err) {
    return { srcFile, status: "error", reason: "check_test_exception", error: err };
  }
}



function isDafnyAvailable() {
  const pathEnv = process.env.PATH || '';
  const dirs = pathEnv.split(path.delimiter);
  for (const dir of dirs) {
    const candidate = path.join(dir, 'dafny');
    try {
      fs.accessSync(candidate, fs.constants.X_OK);
      return true;
    } catch (_) {}
  }
  return false;
}

async function runAllTests(opts = {}) {
  const testsRoot = opts.testsRoot || DEFAULT_TESTS_ROOT;
  console.log(`Searching for .dfy files under: ${testsRoot}`);

  if (!isDafnyAvailable()) {
    console.error('Dafny CLI not found in PATH');
    process.exitCode = 2;
    return { results: [], summary: { total: 0, passed: 0, failed: 0, skipped: 0, dafnyFailures: 0, errors: 0 } };
  }

  if (!fs.existsSync(testsRoot)) {
    console.error(`Folder not found: ${testsRoot}`);
    process.exitCode = 2;
    return { results: [], summary: { total: 0, passed: 0, failed: 0, skipped: 0, dafnyFailures: 0, errors: 0 } };
  }

  const dfyFiles = findDfyFiles(testsRoot);
  console.log(`Found ${dfyFiles.length} .dfy file(s).`);
  if (dfyFiles.length === 0) return;

  const concurrency = opts.concurrency || CONCURRENCY;
  console.log(`Running up to ${concurrency} tests in parallel.`);

  const results = [];
  let idx = 0;

  const workers = new Array(Math.min(concurrency, dfyFiles.length)).fill(0).map(async () => {
    while (true) {
      const myIndex = idx++;
      if (myIndex >= dfyFiles.length) return;
      const srcFile = dfyFiles[myIndex];

      // optional: print progress
      console.log(`run (${myIndex + 1}/${dfyFiles.length}): ${srcFile}`);

      // decide whether this test is expected to be a bug (optional)
      const isBug = srcFile.includes("bug_");
      const startTime = performance.now();
      const res = await runTest(srcFile);
      const duration = (performance.now() - startTime) / 1000;

      if (res.reason === "timeout") {
        res.status = "failed";
      }
   
      if(res.status == "error" || 
          (isBug && res.status == "passed") ||
          (!isBug && res.status == "failed")
      ){
           console.error(`Test Failed: ${srcFile}. Reasons: ${res.reason}`)
      }
      
      results.push({ srcFile, res, isBug, duration, lineStatus: res.lineStatus || [] });
    }
  });

  // wait for all workers to finish
  await Promise.all(workers);

  // Aggregate results
  let total = results.length;
  let passed = 0,
    failed = 0,
    skipped = 0,
    dafnyFailures = 0,
    errors = 0;

  for (const { srcFile, res, isBug } of results) {
    if (!res) {
      errors += 1;
      console.error(`No result for ${srcFile}`);
      continue;
    }
    switch (res.status) {
      case "passed":
        if (!isBug) passed += 1;
        else failed += 1; // a bug that passed counts as failure
        break;
      case "failed":
        if (isBug) passed += 1; // expected failure
        else failed += 1;
        break;
      case "skipped":
        skipped += 1;
        if (res.reason === "dafny_failed") dafnyFailures += 1;
        break;
      case "error":
      default:
        errors += 1;
        break;
    }
  }

  console.log("\n================== Summary ==================");
  console.log(`Total .dfy files found: ${dfyFiles.length}`);
  console.log(`Passed: ${passed}`);
  console.log(`Failed: ${failed}`);
  console.log(`Skipped: ${skipped}`);
  console.log(`Dafny invocation failures: ${dafnyFailures}`);
  console.log(`Other errors: ${errors}`);

  if (failed > 0 || dafnyFailures > 0 || errors > 0) {
    console.error("One or more tests failed or Dafny runs failed.");
    process.exitCode = 1;
  } else {
    console.log("All tests passed and Dafny runs succeeded.");
    process.exitCode = 0;
  }

  return { results, summary: { total: dfyFiles.length, passed, failed, skipped, dafnyFailures, errors } };
}

export { runAllTests };


