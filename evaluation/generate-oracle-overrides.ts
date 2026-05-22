/**
 * Generates evaluation/oracle-overrides.json pre-populated with all tasks.
 * Each entry has the original oracle classification and an override initialized
 * to the same value. Edit the "override" fields when you find oracle errors.
 *
 * Usage: npx tsx evaluation/generate-oracle-overrides.ts
 */
import * as fs from "node:fs";
import * as path from "node:path";

interface OracleLabels {
  postcondition?: "strong" | "weak" | "wrong";
  invariant?: "strong" | "weak";
  precondition?: "required" | "optional";
}

interface RawOracleEntry {
  task_id: string;
  isVerified: boolean;
  note: string;
  dafny_code: string;
}

interface ResultEntry {
  taskId: string;
  filePath: string;
  classification: string;
  categories: {
    postcondition: "strong" | "weak" | "none";
    precondition: "required" | "optional" | "none";
    invariant: "strong" | "weak" | "none";
  };
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

function extractLabels(note: string): OracleLabels {
  const labels: OracleLabels = {};
  if (/\[STRONG-POST\]/.test(note)) labels.postcondition = "strong";
  else if (/\[WEAK-POST\]/.test(note)) labels.postcondition = "weak";
  else if (/\[WRONG\]/.test(note)) labels.postcondition = "wrong";
  if (/\[STRONG-INV\]/.test(note)) labels.invariant = "strong";
  else if (/\[WEAK-INV\]/.test(note)) labels.invariant = "weak";
  if (/\[REQUIRED-PRE\]/.test(note)) labels.precondition = "required";
  else if (/\[OPTIONAL-PRE\]/.test(note)) labels.precondition = "optional";
  return labels;
}

const DATASETS = [
  { id: "RQ1-GPT4", oraclePath: "dafny-synthesis/RQs/RQ1-[Contextless-Prompting]/rq1-GPT-4-temp_0.75-verified-unverified-up.json" },
  { id: "RQ1-PaLM2", oraclePath: "dafny-synthesis/RQs/RQ1-[Contextless-Prompting]/rq1-PaLM-2-temp_0.0-verified-unverified-up.json" },
  { id: "RQ2-GPT4", oraclePath: "dafny-synthesis/RQs/RQ2-[Signature-Prompting]/rq2-GPT-4-temp_0.75-verified-unverified-up.json" },
  { id: "RQ2-PaLM2", oraclePath: "dafny-synthesis/RQs/RQ2-[Signature-Prompting]/rq2-PaLM-2-temp_0.5-verified-unverified-up.json" },
  { id: "RQ3-GPT4", oraclePath: "dafny-synthesis/RQs/RQ3-[Dynamic-Few-Shot-Prompting]/rq3-GPT-4-temp_0.5-verified-unverified-up.json" },
  { id: "RQ3-PaLM2", oraclePath: "dafny-synthesis/RQs/RQ3-[Dynamic-Few-Shot-Prompting]/rq3-PaLM-2-temp_0.5-verified-unverified.json-up.json" },
];

const repoRoot = process.cwd();

function loadOracleLabels(oraclePath: string): Map<string, OracleLabels> {
  const fullPath = path.join(repoRoot, oraclePath);
  if (!fs.existsSync(fullPath)) return new Map();
  const raw: Record<string, RawOracleEntry> = JSON.parse(fs.readFileSync(fullPath, "utf-8"));
  const map = new Map<string, OracleLabels>();
  for (const [, entry] of Object.entries(raw)) {
    if (!entry.isVerified) continue;
    map.set(entry.task_id, extractLabels(entry.note ?? ""));
  }
  return map;
}

function loadResults(datasetId: string): BenchmarkResults | null {
  const p1 = path.join(repoRoot, `evaluation/results/benchmark-results-${datasetId}.json`);
  const p2 = path.join(repoRoot, `evaluation/results/benchmark-results-${datasetId}-minimized.json`);
  const p = fs.existsSync(p1) ? p1 : p2;
  if (!fs.existsSync(p)) return null;
  return JSON.parse(fs.readFileSync(p, "utf-8"));
}

// Build the overrides map
const entries: Record<string, OverrideEntry> = {};

for (const ds of DATASETS) {
  const results = loadResults(ds.id);
  if (!results) { console.warn(`No results for ${ds.id}`); continue; }
  const oracleMap = loadOracleLabels(ds.oraclePath);

  for (const r of results.results) {
    if (r.classification === "error") continue;
    const oracle = oracleMap.get(r.taskId);
    if (!oracle) continue;

    const key = `${ds.id}/${r.taskId}`;
    const oracleObj: OverrideEntry["oracle"] = {};
    const overrideObj: OverrideEntry["override"] = {};

    if (oracle.postcondition) {
      oracleObj.postcondition = oracle.postcondition;
      overrideObj.postcondition = oracle.postcondition;
    }
    if (oracle.precondition) {
      oracleObj.precondition = oracle.precondition;
      overrideObj.precondition = oracle.precondition;
    }
    if (oracle.invariant) {
      oracleObj.invariant = oracle.invariant;
      overrideObj.invariant = oracle.invariant;
    }

    entries[key] = { oracle: oracleObj, override: overrideObj };
  }
}

const output = {
  _comment: "Oracle labels with overrides. 'oracle' = original label from dataset. 'override' = effective label used for evaluation. Edit 'override' when you find oracle errors.",
  entries,
};

const outPath = path.join(repoRoot, "evaluation/oracle-overrides.json");
fs.writeFileSync(outPath, JSON.stringify(output, null, 2) + "\n");
console.log(`Written ${outPath} (${Object.keys(entries).length} entries)`);
