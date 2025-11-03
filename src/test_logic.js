import { createRequire } from 'module';
const require = createRequire(import.meta.url);
const fs = require('fs');
const path = require("path");
const { spawnSync } = require("child_process");

import spans from './spans_provider.js'; // default import from CJS module
const {
    parseProof
} = spans;

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
    if(expected.size < 1){
       console.error("Failed ", name, ": expect comments are empty");
       test_passed = false;
    }
    for (const [lineNum, expectedStatus] of expected.entries()) {
        if (lineNum < 1 || lineNum > received.length) {
            test_passed = false;
            console.error(`Failed '${name}' failed: Line ${lineNum} is out of bounds (received has ${received.length} lines).`);
        }

        const actualStatus = received[lineNum - 1];

        if (actualStatus !== expectedStatus) {
            test_passed = false;
            console.error(`Failed '${name}': Line ${lineNum} expected '${expectedStatus}', but got '${actualStatus}'.`);
        }
    }
    if(test_passed){
        console.log("Passed ", name);
    }
    return test_passed;
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

function runDafnyAndAppendLog(srcFilePath) {
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
  ];

  //console.log(`Running: dafny ${args.join(" ")}  (cwd: ${dir})`);

  // spawnSync with cwd ensures dafny runs from the source file's directory.
  // We capture stdout/stderr and append them to prover_log.txt.
  try {
    const proc = spawnSync("dafny", args, { cwd: dir, encoding: "utf8", timeout: 10 * 1000 }); // 10 secmin timeout
    const { status, error, stdout, stderr } = proc;

    // Compose a header to make logs per-run clear
    const header = `\n===== dafny run for ${fileName} (${new Date().toISOString()}) =====\n`;
    const footer = `\n===== end dafny run for ${fileName} =====\n`;

    // Always append whatever we received to prover_log.txt
    try {
      fs.appendFileSync(proverLogPath, header, "utf8");
      if (stdout && stdout.length) fs.appendFileSync(proverLogPath, stdout, "utf8");
      if (stderr && stderr.length) fs.appendFileSync(proverLogPath, stderr, "utf8");
      fs.appendFileSync(proverLogPath, footer, "utf8");
    } catch (writeErr) {
      console.error(`Failed to append dafny output to ${proverLogPath}:`, writeErr);
      return { ok: false, reason: "append_failed", writeErr };
    }

    if (error) {
      // spawnSync-level error (e.g., command not found)
      console.error(`Error invoking dafny for ${fileName}:`, error);
      return { ok: false, reason: "spawn_error", error };
    }

    if (status !== 0) {
      // dafny returned non-zero exit code. We still appended output; caller decides what to do.
      console.warn(`dafny exited with code ${status} for ${fileName}. See ${proverLogPath} for details.`);
      return { ok: true, code: status, note: "nonzero_exit" };
    }

    // success
    return { ok: true, code: status };
  } catch (err) {
    console.error(`Unexpected error while running dafny on ${srcFilePath}:`, err);
    return { ok: false, reason: "exception", error: err };
  }
}


function runAllTests(opts = {}) {
  const testsRoot = opts.testsRoot || path.join("dataset", "tests");
  console.log(`Searching for .dfy files under: ${testsRoot}`);

  if (!fs.existsSync(testsRoot)) {
    console.error(`Folder not found: ${testsRoot}`);
    process.exitCode = 2;
    return;
  }

  const dfyFiles = findDfyFiles(testsRoot);
  console.log(`Found ${dfyFiles.length} .dfy file(s).`);
 let total = 0;
  let passed = 0;
  let failed = 0;
  let skipped = 0;
  let dafnyFailures = 0;

  console.log("\n");
  for (const srcFile of dfyFiles) {
    total += 1;
    console.log("--------------------------------------------------");
    //console.log(`Processing: ${srcFile}`);

    const dir = path.dirname(srcFile);
    const proofFile = path.join(dir, "prover_log.txt");

    // If proofFile exists delete that file
    if (fs.existsSync(proofFile)) {
      fs.unlinkSync(proofFile);
    }
    // 1) Run Dafny in that directory and append to prover_log.txt
    const dafnyRes = runDafnyAndAppendLog(srcFile);
    if (!dafnyRes.ok) {
      dafnyFailures += 1;
      console.error(`Failed to run dafny for ${srcFile} (reason: ${dafnyRes.reason || "unknown"}). Skipping parsing/checking for this file.`);
      skipped += 1;
      continue;
    }

    // 2) Read source and the (newly appended) prover log
    let src, log;
    try {
      src = fs.readFileSync(srcFile, "utf-8");
    } catch (err) {
      console.error(`Failed to read source file ${srcFile}:`, err);
      failed += 1;
      continue;
    }

    try {
      log = fs.readFileSync(proofFile, "utf-8");
    } catch (err) {
      console.error(`Failed to read proof file ${proofFile}:`, err);
      failed += 1;
      continue;
    }

    // 3) parseProof & parse_test (assumed available in scope)
    let proofTest, parsedTest;
    try {
      proofTest = parseProof(src, log); // should return { lineStatus: [...] }
    } catch (err) {
      console.error(`Error while parsing proof for ${srcFile}:`, err);
      failed += 1;
      continue;
    }

    try {
      parsedTest = parse_test(src); // expected to return [test_name, testExpectedOut]
    } catch (err) {
      console.error(`Error while parsing test metadata from ${srcFile}:`, err);
      failed += 1;
      continue;
    }

    if (!Array.isArray(parsedTest) || parsedTest.length < 2) {
      console.error(`parse_test did not return [name, expectedMap] for ${srcFile}. Got:`, parsedTest);
      failed += 1;
      continue;
    }

    const [test_name, testExpectedOut] = parsedTest;

    // Validate expected map type
    if (!(testExpectedOut instanceof Map)) {
      console.error(
        `Expected a Map from parse_test for ${srcFile}, but got ${Object.prototype.toString.call(
          testExpectedOut
        )}.`
      );
      failed += 1;
      continue;
    }

    const lineStatus = (proofTest && proofTest.lineStatus) || [];

    try {
      const ok = check_test(srcFile, testExpectedOut, lineStatus);
      if (ok) passed += 1;
      else failed += 1;
    } catch (err) {
      console.error(`Exception while checking test for ${srcFile}:`, err);
      failed += 1;
    }
  }

  console.log("\n================== Summary ==================");
  console.log(`Total .dfy files found: ${total}`);
  console.log(`Passed: ${passed}`);
  console.log(`Failed: ${failed}`);
  console.log(`Skipped (dafny/spawn/parse issues): ${skipped}`);
  console.log(`Dafny invocation failures: ${dafnyFailures}`);

  if (failed > 0 || dafnyFailures > 0) {
    console.error("One or more tests failed or Dafny runs failed.");
    process.exitCode = 1;
  } else {
    console.log("All tests passed and Dafny runs succeeded.");
  }
}

runAllTests();

//const proofFile = "src/prover_log.txt";
//const sourceFile = "src/source_code.dfy";

//const src = fs.readFileSync(sourceFile, "utf-8");
//const log = fs.readFileSync(proofFile, "utf-8");
//
//const proofTest = parseProof(src, log);
//const [test_name, testExpectedOut] = parse_test(src);
//const lineStatus = proofTest.lineStatus;
//check_test(test_name,testExpectedOut, lineStatus);
// maybe run assertions etc