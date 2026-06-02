#!/usr/bin/env tsx
/**
 * Debug script: run evaluation on a single .dfy file with verbose logging.
 *
 * Usage:
 *   npx tsx evaluation/src/debug-single.ts <path-to-dfy-file> [--dafny-path <path>] [--timeout <seconds>]
 *
 * Outputs:
 *   1. YAML representation of the proof graph
 *   2. Step-by-step classification reasoning
 */
import * as fs from "node:fs";
import {
  runDafny,
  parseProof,
  TokenType,
  CovStatus,
  type NodeData,
} from "@proofpulse/core";
import { classifyPostcondition, classifyInvariant, classifyPrecondition, classifySpec, classifyAll } from "./classifier.js";

// ─── CLI parsing ───────────────────────────────────────────────────────────
const args = process.argv.slice(2);
let filePath = "";
let dafnyPath = "dafny";
let timeout = 60;

for (let i = 0; i < args.length; i++) {
  if (args[i] === "--dafny-path") { dafnyPath = args[++i]; continue; }
  if (args[i] === "--timeout") { timeout = Number(args[++i]); continue; }
  if (args[i] === "--help" || args[i] === "-h") {
    console.log("Usage: npx tsx evaluation/src/debug-single.ts <file.dfy> [--dafny-path <path>] [--timeout <s>]");
    process.exit(0);
  }
  if (!filePath) filePath = args[i];
}

if (!filePath) {
  console.error("Error: no .dfy file specified");
  process.exit(1);
}
if (!fs.existsSync(filePath)) {
  console.error(`Error: file not found: ${filePath}`);
  process.exit(1);
}

// ─── Helpers ───────────────────────────────────────────────────────────────
const SEP = "═".repeat(70);
const LINE = "─".repeat(70);

function statusIcon(s: CovStatus): string {
  if (s === CovStatus.CovComplete) return "✓";
  if (s === CovStatus.CovTest) return "~";
  return "✗";
}

// ─── Main ──────────────────────────────────────────────────────────────────
async function main() {
  console.log(SEP);
  console.log(`DEBUG SINGLE FILE: ${filePath}`);
  console.log(SEP);

  // Step 1: Run Dafny
  console.log("\n[1] Running Dafny verification...");
  const dafnyResult = await runDafny(filePath, { dafnyPath, timeoutSeconds: timeout });

  if (dafnyResult.error || dafnyResult.timedOut) {
    console.error(`Dafny failed: ${dafnyResult.error ?? "timeout"}`);
    process.exit(1);
  }
  console.log(`    Exit code: ${dafnyResult.exitCode}`);
  console.log(`    Log length: ${dafnyResult.log.length} chars`);

  // Step 2: Parse proof (builds graph + applies coverage)
  console.log("\n[2] Parsing proof & building graph...");
  const sourceCode = fs.readFileSync(filePath, "utf-8");
  const proof = parseProof(sourceCode, dafnyResult.log);
  const graph = proof.proofGraph;

  // Step 3: Dump YAML
  console.log(`\n[3] Proof Graph YAML:\n${LINE}`);
  console.log(graph.toYAML());
  console.log(LINE);

  // Step 4: Classification steps
  const allNodes = graph.getAllNodes();
  const topNodes = graph.getAllTopNodes();

  console.log(`\n[4] Graph summary:`);
  console.log(`    Total nodes: ${allNodes.length}`);
  console.log(`    Top nodes: ${topNodes.length}`);

  // ── Postcondition classification steps ──
  console.log(`\n[5] Postcondition classification steps:`);
  const postTops = topNodes.filter(n => n.getType() === TokenType.Postcondition);
  console.log(`    Postcondition tops found: ${postTops.length}`);
  if (postTops.length === 0) {
    console.log(`    → Result: "none" (no postcondition tops)`);
  } else {
    const methodTops = postTops.filter(n => !n.methodType.includes("well-formedness"));
    const wfTops = postTops.filter(n => n.methodType.includes("well-formedness"));
    console.log(`    Well-formedness tops (skipped): ${wfTops.length}`);
    console.log(`    Method/correctness tops: ${methodTops.length}`);

    if (methodTops.length === 0) {
      console.log(`    → Result: "strong" (only well-formedness tops)`);
    } else {
      let weakReason = "";
      for (const top of methodTops) {
        const deps = new Set([...top.provedBy, ...top.proofUnused]);
        console.log(`\n    Top [${top.start.line}:${top.start.col}] methodType="${top.methodType}"`);
        console.log(`      provedBy: ${top.provedBy.size} nodes, proofUnused: ${top.proofUnused.size} nodes`);
        console.log(`      Combined deps: ${deps.size}`);
        if (deps.size === 0) {
          console.log(`      ⚠ Empty deps → WEAK (tautology/unproven)`);
          weakReason = weakReason || `top at line ${top.start.line} has empty deps`;
        }
        for (const dep of deps) {
          const icon = statusIcon(dep.covStatus);
          const isCodeLine = dep.getType() === TokenType.CodeLine;
          const tag = isCodeLine ? "" : " [IGNORED: not CodeLine]";
          console.log(`      ${icon} dep [${dep.start.line}:${dep.start.col}] type=${dep.getType()} covStatus=${dep.covStatus} methodType="${dep.methodType}"${tag}`);
          if (isCodeLine && dep.covStatus === CovStatus.Uncovered && !weakReason) {
            weakReason = `CodeLine dep at line ${dep.start.line} is Uncovered`;
          }
        }
      }
      const postResult = classifyPostcondition(graph);
      console.log(`\n    → Postcondition result: "${postResult}"${weakReason ? ` (reason: ${weakReason})` : ""}`);
    }
  }

  // ── Invariant classification steps ──
  console.log(`\n[6] Invariant classification steps:`);
  const invTops = topNodes.filter(n => n.getType() === TokenType.LoopInvariant);
  console.log(`    Invariant tops found: ${invTops.length}`);
  if (invTops.length === 0) {
    console.log(`    → Result: "none" (no invariant tops)`);
  } else {
    const methodTops = invTops.filter(n => !n.methodType.includes("well-formedness"));
    const wfTops = invTops.filter(n => n.methodType.includes("well-formedness"));
    console.log(`    Well-formedness tops (skipped): ${wfTops.length}`);
    console.log(`    Method/correctness tops: ${methodTops.length}`);

    if (methodTops.length === 0) {
      console.log(`    → Result: "strong" (only well-formedness tops)`);
    } else {
      let weakReason = "";
      for (const top of methodTops) {
        const deps = new Set([...top.provedBy, ...top.proofUnused]);
        console.log(`\n    Top [${top.start.line}:${top.start.col}] methodType="${top.methodType}"`);
        console.log(`      provedBy: ${top.provedBy.size} nodes, proofUnused: ${top.proofUnused.size} nodes`);
        console.log(`      Combined deps: ${deps.size}`);
        if (deps.size === 0) {
          console.log(`      ⚠ Empty deps → WEAK (tautology/unproven)`);
          weakReason = weakReason || `top at line ${top.start.line} has empty deps`;
        }
        for (const dep of deps) {
          const icon = statusIcon(dep.covStatus);
          const isCodeLine = dep.getType() === TokenType.CodeLine;
          const tag = isCodeLine ? "" : " [IGNORED: not CodeLine]";
          console.log(`      ${icon} dep [${dep.start.line}:${dep.start.col}] type=${dep.getType()} covStatus=${dep.covStatus} methodType="${dep.methodType}"${tag}`);
          if (isCodeLine && dep.covStatus === CovStatus.Uncovered && !weakReason) {
            weakReason = `CodeLine dep at line ${dep.start.line} is Uncovered`;
          }
        }
      }
      const invResult = classifyInvariant(graph);
      console.log(`\n    → Invariant result: "${invResult}"${weakReason ? ` (reason: ${weakReason})` : ""}`);
    }
  }

  // ── Precondition classification steps ──
  console.log(`\n[7] Precondition classification steps:`);
  const preNodes = allNodes.filter(n => n.getType() === TokenType.Precondition);
  console.log(`    Precondition nodes: ${preNodes.length}`);
  const preMethodNodes = preNodes.filter(n => !n.methodType.includes("well-formedness"));
  const preWfNodes = preNodes.filter(n => n.methodType.includes("well-formedness"));
  console.log(`    Well-formedness (skipped): ${preWfNodes.length}`);
  console.log(`    Method/correctness: ${preMethodNodes.length}`);
  for (const n of preNodes) {
    const icon = statusIcon(n.covStatus);
    const skipped = n.methodType.includes("well-formedness") ? " [SKIPPED]" : "";
    console.log(`    ${icon} [${n.start.line}:${n.start.col}] covStatus=${n.covStatus} methodType="${n.methodType}"${skipped}`);
  }
  const preResult = classifyPrecondition(allNodes as NodeData[]);
  console.log(`    → Precondition result: "${preResult}"`);

  // ── Overall ──
  console.log(`\n[8] Overall classification:`);
  const categories = classifyAll(graph, allNodes as NodeData[]);
  const overall = classifySpec(graph);
  console.log(`    postcondition: ${categories.postcondition}`);
  console.log(`    precondition:  ${categories.precondition}`);
  console.log(`    invariant:     ${categories.invariant}`);
  console.log(`    overall:       ${overall}`);
  console.log(`\n${SEP}`);
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
