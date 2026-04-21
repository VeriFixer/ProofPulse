import * as fs from "node:fs";
import * as path from "node:path";

export interface OracleLabels {
  postcondition?: "strong" | "weak" | "wrong";
  invariant?: "strong" | "weak";
  precondition?: "required" | "optional";
}

export interface OracleEntry {
  taskId: string;
  filePath: string;
  label: "strong" | "weak" | "wrong";
  labels: OracleLabels;
  dataset: string;
  dafnyCode: string;
}

export type DatasetId =
  | "RQ1-GPT4"
  | "RQ1-PaLM2"
  | "RQ2-GPT4"
  | "RQ2-PaLM2"
  | "RQ3-GPT4"
  | "RQ3-PaLM2";

export const ALL_DATASETS: { id: DatasetId; relPath: string }[] = [
  { id: "RQ1-GPT4", relPath: "RQs/RQ1-[Contextless-Prompting]/rq1-GPT-4-temp_0.75-verified-unverified-up.json" },
  { id: "RQ1-PaLM2", relPath: "RQs/RQ1-[Contextless-Prompting]/rq1-PaLM-2-temp_0.0-verified-unverified-up.json" },
  { id: "RQ2-GPT4", relPath: "RQs/RQ2-[Signature-Prompting]/rq2-GPT-4-temp_0.75-verified-unverified-up.json" },
  { id: "RQ2-PaLM2", relPath: "RQs/RQ2-[Signature-Prompting]/rq2-PaLM-2-temp_0.5-verified-unverified-up.json" },
  { id: "RQ3-GPT4", relPath: "RQs/RQ3-[Dynamic-Few-Shot-Prompting]/rq3-GPT-4-temp_0.5-verified-unverified-up.json" },
  { id: "RQ3-PaLM2", relPath: "RQs/RQ3-[Dynamic-Few-Shot-Prompting]/rq3-PaLM-2-temp_0.5-verified-unverified.json-up.json" },
];

const DFY_SRC_REL_PATH = "MBPP-DFY-153/src";

interface RawOracleEntry {
  task_id: string;
  isVerified: boolean;
  note: string;
  dafny_code: string;
}

export function extractLabels(note: string): OracleLabels {
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

function overallLabel(labels: OracleLabels): "strong" | "weak" | "wrong" | null {
  if (labels.postcondition === "strong") return "strong";
  if (labels.postcondition === "weak") return "weak";
  if (labels.postcondition === "wrong") return "wrong";
  return null;
}

/**
 * Parse oracle for a specific dataset. If no dataset specified, uses RQ3-GPT4 (default).
 * For RQ3-GPT4, uses .dfy files from MBPP-DFY-153/src/.
 * For other datasets, writes dafny_code to a temp directory.
 */
export function parseOracle(repoRoot: string, datasetId?: DatasetId): OracleEntry[] {
  const dataset = ALL_DATASETS.find((d) => d.id === (datasetId ?? "RQ3-GPT4"))!;
  const oraclePath = path.join(repoRoot, dataset.relPath);
  const dfySrcDir = path.join(repoRoot, DFY_SRC_REL_PATH);

  if (!fs.existsSync(oraclePath)) {
    console.warn(`[oracle-parser] JSON not found: ${oraclePath}`);
    return [];
  }

  const raw: Record<string, RawOracleEntry> = JSON.parse(
    fs.readFileSync(oraclePath, "utf-8"),
  );

  const entries: OracleEntry[] = [];

  // Create temp dir for inline code outside the submodule
  const tempDir = path.join(path.dirname(repoRoot), ".eval-tmp", dataset.id);
  fs.mkdirSync(tempDir, { recursive: true });

  for (const [_key, entry] of Object.entries(raw)) {
    const taskId = entry.task_id;
    if (!entry.isVerified) continue;

    const labels = extractLabels(entry.note ?? "");
    const label = overallLabel(labels);
    if (label === null) {
      console.warn(`[oracle-parser] Skipping ${dataset.id}/task_${taskId}: no postcondition tag`);
      continue;
    }

    const dafnyCode = entry.dafny_code ?? "";
    if (!dafnyCode.trim()) {
      console.warn(`[oracle-parser] Skipping ${dataset.id}/task_${taskId}: empty dafny_code`);
      continue;
    }

    // Try MBPP-DFY-153/src first, fall back to writing temp file
    let filePath: string;
    const dfyFile = path.join(dfySrcDir, `task_id_${taskId}.dfy`);
    if (datasetId === "RQ3-GPT4" && fs.existsSync(dfyFile)) {
      filePath = path.resolve(dfyFile);
    } else {
      // Write inline code to temp file
      const tempFile = path.join(tempDir, `task_id_${taskId}.dfy`);
      fs.writeFileSync(tempFile, dafnyCode);
      filePath = path.resolve(tempFile);
    }

    entries.push({ taskId, filePath, label, labels, dataset: dataset.id, dafnyCode });
  }

  return entries;
}

/** Parse all datasets and return combined entries grouped by dataset. */
export function parseAllOracles(repoRoot: string): Map<DatasetId, OracleEntry[]> {
  const result = new Map<DatasetId, OracleEntry[]>();
  for (const ds of ALL_DATASETS) {
    result.set(ds.id, parseOracle(repoRoot, ds.id));
  }
  return result;
}
