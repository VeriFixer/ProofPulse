/**
 * Automated report: generates results.md with:
 * 1. Full results table (all files, all datasets)
 * 2. Divergences grouped by category and direction (FP vs FN)
 *
 * Uses evaluation/oracle-overrides.json as the single source of truth for oracle labels.
 * The "override" field is what's used for matching. When override != oracle, the table
 * shows pred/oracle/overridden format.
 *
 * Usage: npx tsx evaluation/generate-results-md.ts
 */
import * as fs from "node:fs";
import * as path from "node:path";

interface CategoryClassification {
  postcondition: "strong" | "weak" | "none";
  precondition: "required" | "optional" | "none";
  invariant: "strong" | "weak" | "none";
}

interface ResultEntry {
  taskId: string;
  filePath: string;
  classification: string;
  categories: CategoryClassification;
  oracleLabel: string;
  postconditionLines: number[];
  preconditionLines: number[];
  invariantLines: number[];
  bodyLines: number[];
  coverageStatuses: Record<string, string>;
  durationMs: number;
  error?: string;
}

interface BenchmarkResults {
  results: ResultEntry[];
}

interface OverrideEntry {
  oracle: {
    postcondition?: string;
    precondition?: string;
    invariant?: string;
  };
  override: {
    postcondition?: string;
    precondition?: string;
    invariant?: string;
  };
}

interface OracleOverridesFile {
  _comment?: string;
  entries: Record<string, OverrideEntry>;
}

const DATASETS = [
  "RQ1-GPT4", "RQ1-PaLM2", "RQ2-GPT4", "RQ2-PaLM2", "RQ3-GPT4", "RQ3-PaLM2",
];

interface Divergence {
  dataset: string;
  taskId: string;
  category: "postcondition" | "precondition" | "invariant";
  direction: "FP" | "FN";
  predicted: string;
  oracle: string;
  override: string;
  relativePath: string;
}

const repoRoot = process.cwd();

// Load oracle overrides (single source of truth)
function loadOracleOverrides(): OracleOverridesFile {
  const overridesPath = path.join(repoRoot, "evaluation/oracle-overrides.json");
  if (!fs.existsSync(overridesPath)) {
    console.error("ERROR: evaluation/oracle-overrides.json not found.");
    console.error("Run: npx tsx evaluation/generate-oracle-overrides.ts");
    process.exit(1);
  }
  return JSON.parse(fs.readFileSync(overridesPath, "utf-8"));
}

function loadResults(datasetId: string): BenchmarkResults | null {
  const p1 = path.join(repoRoot, `evaluation/results/benchmark-results-${datasetId}.json`);
  const p2 = path.join(repoRoot, `evaluation/results/benchmark-results-${datasetId}-minimized.json`);
  const p = fs.existsSync(p1) ? p1 : p2;
  if (!fs.existsSync(p)) return null;
  return JSON.parse(fs.readFileSync(p, "utf-8"));
}

function makeRelativePath(filePath: string): string {
  return path.relative(repoRoot, filePath);
}

// Collect data
interface EntryRow {
  dataset: string;
  taskId: string;
  relativePath: string;
  postPred: string;
  postOracle: string;
  postOverride: string;
  prePred: string;
  preOracle: string;
  preOverride: string;
  invPred: string;
  invOracle: string;
  invOverride: string;
  postMatch: boolean;
  preMatch: boolean;
  invMatch: boolean;
}

const overridesFile = loadOracleOverrides();
const entries = overridesFile.entries;

const allEntries: EntryRow[] = [];
const allDivergences: Divergence[] = [];

// Confusion matrix accumulators
let postTP = 0, postFP = 0, postFN = 0, postTN = 0;
let preTP = 0, preFP = 0, preFN = 0, preTN = 0;
let invTP = 0, invFP = 0, invFN = 0, invTN = 0;

for (const dsId of DATASETS) {
  const results = loadResults(dsId);
  if (!results) { console.warn(`No results for ${dsId}`); continue; }

  for (const r of results.results) {
    if (r.classification === "error") continue;

    const key = `${dsId}/${r.taskId}`;
    const entry = entries[key];
    if (!entry) continue;

    const relativePath = makeRelativePath(r.filePath);
    const postPred = r.categories.postcondition;
    const postOracle = entry.oracle.postcondition ?? "-";
    const postOverride = entry.override.postcondition ?? "-";
    const prePred = r.categories.precondition;
    const preOracle = entry.oracle.precondition ?? "-";
    const preOverride = entry.override.precondition ?? "-";
    const invPred = r.categories.invariant;
    const invOracle = entry.oracle.invariant ?? "-";
    const invOverride = entry.override.invariant ?? "-";

    // Match against override (the effective label)
    let postMatch = true;
    if (postOverride !== "-" && postOverride !== "wrong") {
      const pred = postPred === "strong";
      const actual = postOverride === "strong";
      postMatch = pred === actual;
      if (pred && actual) postTP++;
      else if (pred && !actual) { postFP++; allDivergences.push({ dataset: dsId, taskId: r.taskId, category: "postcondition", direction: "FP", predicted: postPred, oracle: postOracle, override: postOverride, relativePath }); }
      else if (!pred && actual) { postFN++; allDivergences.push({ dataset: dsId, taskId: r.taskId, category: "postcondition", direction: "FN", predicted: postPred, oracle: postOracle, override: postOverride, relativePath }); }
      else postTN++;
    }

    let preMatch = true;
    if (preOverride !== "-" && prePred !== "none") {
      const pred = prePred === "required";
      const actual = preOverride === "required";
      preMatch = pred === actual;
      if (pred && actual) preTP++;
      else if (pred && !actual) { preFP++; allDivergences.push({ dataset: dsId, taskId: r.taskId, category: "precondition", direction: "FP", predicted: prePred, oracle: preOracle, override: preOverride, relativePath }); }
      else if (!pred && actual) { preFN++; allDivergences.push({ dataset: dsId, taskId: r.taskId, category: "precondition", direction: "FN", predicted: prePred, oracle: preOracle, override: preOverride, relativePath }); }
      else preTN++;
    }

    let invMatch = true;
    if (invOverride !== "-" && invPred !== "none") {
      const pred = invPred === "strong";
      const actual = invOverride === "strong";
      invMatch = pred === actual;
      if (pred && actual) invTP++;
      else if (pred && !actual) { invFP++; allDivergences.push({ dataset: dsId, taskId: r.taskId, category: "invariant", direction: "FP", predicted: invPred, oracle: invOracle, override: invOverride, relativePath }); }
      else if (!pred && actual) { invFN++; allDivergences.push({ dataset: dsId, taskId: r.taskId, category: "invariant", direction: "FN", predicted: invPred, oracle: invOracle, override: invOverride, relativePath }); }
      else invTN++;
    }

    allEntries.push({ dataset: dsId, taskId: r.taskId, relativePath, postPred, postOracle, postOverride, prePred, preOracle, preOverride, invPred, invOracle, invOverride, postMatch, preMatch, invMatch });
  }
}

// --- Generate Markdown ---
const lines: string[] = [];

lines.push("# ProofPulse Evaluation Results");
lines.push("");
lines.push("Auto-generated by `npx tsx evaluation/generate-results-md.ts`");
lines.push("");

// Summary table
const postP = postTP + postFP === 0 ? 0 : postTP / (postTP + postFP);
const postR = postTP + postFN === 0 ? 0 : postTP / (postTP + postFN);
const postAcc = (postTP + postFP + postFN + postTN) === 0 ? 0 : (postTP + postTN) / (postTP + postFP + postFN + postTN);
const preP = preTP + preFP === 0 ? 0 : preTP / (preTP + preFP);
const preR = preTP + preFN === 0 ? 0 : preTP / (preTP + preFN);
const preAcc = (preTP + preFP + preFN + preTN) === 0 ? 0 : (preTP + preTN) / (preTP + preFP + preFN + preTN);
const invP = invTP + invFP === 0 ? 0 : invTP / (invTP + invFP);
const invR = invTP + invFN === 0 ? 0 : invTP / (invTP + invFN);
const invAcc = (invTP + invFP + invFN + invTN) === 0 ? 0 : (invTP + invTN) / (invTP + invFP + invFN + invTN);

lines.push("## Summary");
lines.push("");
lines.push("| Category | TP | FP | FN | TN | P | R | Acc |");
lines.push("|----------|----|----|----|----|------|------|------|");
lines.push(`| Postconditions | ${postTP} | ${postFP} | ${postFN} | ${postTN} | ${postP.toFixed(2)} | ${postR.toFixed(2)} | ${postAcc.toFixed(2)} |`);
lines.push(`| Preconditions | ${preTP} | ${preFP} | ${preFN} | ${preTN} | ${preP.toFixed(2)} | ${preR.toFixed(2)} | ${preAcc.toFixed(2)} |`);
lines.push(`| Invariants | ${invTP} | ${invFP} | ${invFN} | ${invTN} | ${invP.toFixed(2)} | ${invR.toFixed(2)} | ${invAcc.toFixed(2)} |`);
lines.push("");

// --- Full results table ---
lines.push("## All Results");
lines.push("");

lines.push("| Dataset | Task | File | Post (pred/oracle/override) | Pre (pred/oracle/override) | Inv (pred/oracle/override) | Post ✓ | Pre ✓ | Inv ✓ | Ovr |");
lines.push("|---------|------|------|----------------------------|----------------------------|----------------------------|--------|-------|-------|-----|");

for (const e of allEntries) {
  const fileLink = `[task_${e.taskId}](${e.relativePath})`;
  const postOk = e.postMatch ? "✅" : "❌";
  const preOk = e.preMatch ? "✅" : "❌";
  const invOk = e.invMatch ? "✅" : "❌";

  const postCol = `${e.postPred}/${e.postOracle}/${e.postOverride}`;
  const preCol = `${e.prePred}/${e.preOracle}/${e.preOverride}`;
  const invCol = `${e.invPred}/${e.invOracle}/${e.invOverride}`;

  // Any override differs from oracle for this row?
  const hasOverride =
    (e.postOracle !== "-" && e.postOracle !== e.postOverride) ||
    (e.preOracle !== "-" && e.preOracle !== e.preOverride) ||
    (e.invOracle !== "-" && e.invOracle !== e.invOverride);
  const ovrCol = hasOverride ? "⚠️" : "";

  lines.push(`| ${e.dataset} | ${e.taskId} | ${fileLink} | ${postCol} | ${preCol} | ${invCol} | ${postOk} | ${preOk} | ${invOk} | ${ovrCol} |`);
}

lines.push("");

// --- Divergences by category and direction ---
lines.push("## Divergences");
lines.push("");
lines.push(`Total: ${allDivergences.length} (Post FP=${postFP} FN=${postFN} | Pre FP=${preFP} FN=${preFN} | Inv FP=${invFP} FN=${invFN})`);
lines.push("");

const sections: { title: string; filter: (d: Divergence) => boolean }[] = [
  { title: "Postcondition FN — predicted weak, oracle strong", filter: d => d.category === "postcondition" && d.direction === "FN" },
  { title: "Postcondition FP — predicted strong, oracle weak", filter: d => d.category === "postcondition" && d.direction === "FP" },
  { title: "Precondition FN — predicted optional, oracle required", filter: d => d.category === "precondition" && d.direction === "FN" },
  { title: "Precondition FP — predicted required, oracle optional", filter: d => d.category === "precondition" && d.direction === "FP" },
  { title: "Invariant FN — predicted weak, oracle strong", filter: d => d.category === "invariant" && d.direction === "FN" },
  { title: "Invariant FP — predicted strong, oracle weak", filter: d => d.category === "invariant" && d.direction === "FP" },
];

for (const sec of sections) {
  const items = allDivergences.filter(sec.filter);
  if (items.length === 0) continue;
  lines.push(`### ${sec.title} (${items.length})`);
  lines.push("");
  lines.push("| Dataset | Task | Predicted | Oracle | Override | File |");
  lines.push("|---------|------|-----------|--------|----------|------|");
  for (const item of items) {
    const fileLink = `[task_${item.taskId}.dfy](${item.relativePath})`;
    lines.push(`| ${item.dataset} | ${item.taskId} | ${item.predicted} | ${item.oracle} | ${item.override} | ${fileLink} |`);
  }
  lines.push("");
}

// Write output
const output = lines.join("\n");
const outPath = path.join(repoRoot, "results.md");
fs.writeFileSync(outPath, output);
console.log(`Written ${outPath} (${allEntries.length} entries, ${allDivergences.length} divergences)`);
