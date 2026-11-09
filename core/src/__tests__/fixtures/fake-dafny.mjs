#!/usr/bin/env node
// Stand-in for `dafny verify` with what the runner relies on: like Dafny, it
// writes the text log to stdout only once every method is verified, but to a
// `--log-format "text;LogFileName=…"` file one method at a time.
//
// FAKE_DAFNY_ARGS: file to record the arguments in.
// FAKE_DAFNY_HANG: after the methods, start a child process (its pid goes to
//   FAKE_DAFNY_CHILD_PID) and never finish, like a solver past its time limit.
// FAKE_DAFNY_RUN_MS: how long verifying takes when not hanging (default 0).
import { spawn } from "node:child_process";
import { appendFileSync, writeFileSync } from "node:fs";

const args = process.argv.slice(2);
if (args.includes("--version")) {
  console.log("4.11.0");
  process.exit(0);
}
if (process.env.FAKE_DAFNY_ARGS) writeFileSync(process.env.FAKE_DAFNY_ARGS, JSON.stringify(args));

const block = (name) => [
  "",
  `Results for ${name} (correctness)`,
  "  Overall outcome: Correct",
  "",
  "  Assertion batch 1:",
  "    Outcome: Valid",
  "",
  "    Assertions:",
  `      fake.dfy(1,1)-(1,5): this postcondition holds`,
  "",
].join("\n") + "\n";

const logArg = args[args.indexOf("--log-format") + 1] ?? "";
const logFile = logArg.match(/LogFileName=(.*)$/)?.[1];
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

let stdoutLog = "";
for (const name of ["First", "Second"]) {
  if (logFile) appendFileSync(logFile, block(name));
  else stdoutLog += block(name);
  await sleep(300);
}

if (process.env.FAKE_DAFNY_HANG) {
  const child = spawn(process.execPath, ["-e", "setInterval(() => {}, 1000)"], { stdio: "ignore" });
  writeFileSync(process.env.FAKE_DAFNY_CHILD_PID, String(child.pid));
  setInterval(() => {}, 1000);
} else {
  await sleep(Number(process.env.FAKE_DAFNY_RUN_MS ?? 0));
  process.stdout.write(stdoutLog);
  console.log("\nDafny program verifier finished with 2 verified, 0 errors");
}
