import type { ClassificationResult } from "./classifier.js";
import type { OracleEntry } from "./oracle-parser.js";

export interface ConfusionMatrix {
  tp: number;
  fp: number;
  tn: number;
  fn: number;
}

export interface Metrics {
  precision: number;
  recall: number;
  f1: number;
  accuracy: number;
}

export interface CategoryTable {
  label: string;
  total: number;
  rows: { name: string; predicted: number; oracle: number }[];
  confusionMatrix?: ConfusionMatrix;
  metrics?: Metrics;
}

export function computeConfusionMatrix(results: ClassificationResult[]): ConfusionMatrix {
  const filtered = results.filter((r) => r.classification !== "error" && r.oracleLabel !== "wrong");
  let tp = 0, fp = 0, tn = 0, fn = 0;
  for (const r of filtered) {
    const predicted = r.classification === "strong";
    const actual = r.oracleLabel === "strong";
    if (predicted && actual) tp++;
    else if (predicted && !actual) fp++;
    else if (!predicted && actual) fn++;
    else tn++;
  }
  return { tp, fp, tn, fn };
}

export function computeMetrics(cm: ConfusionMatrix): Metrics {
  const { tp, fp, tn, fn } = cm;
  const precision = tp + fp === 0 ? 0 : tp / (tp + fp);
  const recall = tp + fn === 0 ? 0 : tp / (tp + fn);
  const f1 = precision + recall === 0 ? 0 : (2 * precision * recall) / (precision + recall);
  const total = tp + fp + tn + fn;
  const accuracy = total === 0 ? 0 : (tp + tn) / total;
  return { precision, recall, f1, accuracy };
}

export function formatTable(cm: ConfusionMatrix, metrics: Metrics, results?: ClassificationResult[]): string {
  const lines: string[] = [];
  lines.push("Confusion Matrix (Overall Postcondition, excl. oracle=wrong)");
  lines.push("─────────────────────────────────");
  lines.push("                 Oracle Strong  Oracle Weak");
  lines.push(`  Pred Strong     ${String(cm.tp).padStart(5)}          ${String(cm.fp).padStart(5)}`);
  lines.push(`  Pred Weak       ${String(cm.fn).padStart(5)}          ${String(cm.tn).padStart(5)}`);
  if (results) {
    const wrong = results.filter((r) => r.oracleLabel === "wrong" && r.classification !== "error");
    if (wrong.length > 0) {
      lines.push("");
      lines.push(`Oracle=Wrong (excluded, ${wrong.length} entries):`);
      lines.push(`  ProofPulse said strong: ${wrong.filter((r) => r.classification === "strong").length}  weak: ${wrong.filter((r) => r.classification === "weak").length}`);
    }
  }
  lines.push("");
  lines.push("Metrics");
  lines.push("─────────────────────────────────");
  lines.push(`  Precision:  ${metrics.precision.toFixed(4)}`);
  lines.push(`  Recall:     ${metrics.recall.toFixed(4)}`);
  lines.push(`  F1:         ${metrics.f1.toFixed(4)}`);
  lines.push(`  Accuracy:   ${metrics.accuracy.toFixed(4)}`);
  return lines.join("\n");
}


export function computeCategoryTables(
  results: ClassificationResult[],
  entries: OracleEntry[],
): CategoryTable[] {
  const entryMap = new Map(entries.map((e) => [e.taskId, e]));
  const nonError = results.filter((r) => r.classification !== "error");

  // --- Postconditions ---
  const withPost = nonError.filter((r) => entryMap.get(r.taskId)?.labels.postcondition != null);
  const postForCM = withPost.filter((r) => entryMap.get(r.taskId)!.labels.postcondition !== "wrong");
  let pTP = 0, pFP = 0, pTN = 0, pFN = 0;
  for (const r of postForCM) {
    const pred = r.categories.postcondition === "strong";
    const actual = entryMap.get(r.taskId)!.labels.postcondition === "strong";
    if (pred && actual) pTP++; else if (pred && !actual) pFP++; else if (!pred && actual) pFN++; else pTN++;
  }
  const postCM: ConfusionMatrix = { tp: pTP, fp: pFP, tn: pTN, fn: pFN };
  const postTable: CategoryTable = {
    label: "Postconditions (positive=Strong, excl. oracle=wrong)",
    total: withPost.length,
    rows: [
      { name: "Strong", predicted: withPost.filter((r) => r.categories.postcondition === "strong").length, oracle: withPost.filter((r) => entryMap.get(r.taskId)!.labels.postcondition === "strong").length },
      { name: "Weak", predicted: withPost.filter((r) => r.categories.postcondition === "weak").length, oracle: withPost.filter((r) => entryMap.get(r.taskId)!.labels.postcondition === "weak").length },
      { name: "Wrong (excl.)", predicted: 0, oracle: withPost.filter((r) => entryMap.get(r.taskId)!.labels.postcondition === "wrong").length },
      { name: "None (no nodes)", predicted: withPost.filter((r) => r.categories.postcondition === "none").length, oracle: 0 },
    ],
    confusionMatrix: postCM, metrics: computeMetrics(postCM),
  };

  // --- Preconditions ---
  const withPre = nonError.filter((r) => entryMap.get(r.taskId)?.labels.precondition != null);
  const preForCM = withPre.filter((r) => r.categories.precondition !== "none");
  let rTP = 0, rFP = 0, rTN = 0, rFN = 0;
  for (const r of preForCM) {
    const pred = r.categories.precondition === "required";
    const actual = entryMap.get(r.taskId)!.labels.precondition === "required";
    if (pred && actual) rTP++; else if (pred && !actual) rFP++; else if (!pred && actual) rFN++; else rTN++;
  }
  const preCM: ConfusionMatrix = { tp: rTP, fp: rFP, tn: rTN, fn: rFN };
  const preTable: CategoryTable = {
    label: "Preconditions (positive=Required)",
    total: withPre.length,
    rows: [
      { name: "Required", predicted: withPre.filter((r) => r.categories.precondition === "required").length, oracle: withPre.filter((r) => entryMap.get(r.taskId)!.labels.precondition === "required").length },
      { name: "Optional", predicted: withPre.filter((r) => r.categories.precondition === "optional").length, oracle: withPre.filter((r) => entryMap.get(r.taskId)!.labels.precondition === "optional").length },
      { name: "None (no nodes)", predicted: withPre.filter((r) => r.categories.precondition === "none").length, oracle: 0 },
    ],
    confusionMatrix: preCM, metrics: computeMetrics(preCM),
  };

  // --- Invariants ---
  const withInv = nonError.filter((r) => entryMap.get(r.taskId)?.labels.invariant != null);
  const invForCM = withInv.filter((r) => r.categories.invariant !== "none");
  let iTP = 0, iFP = 0, iTN = 0, iFN = 0;
  for (const r of invForCM) {
    const pred = r.categories.invariant === "strong";
    const actual = entryMap.get(r.taskId)!.labels.invariant === "strong";
    if (pred && actual) iTP++; else if (pred && !actual) iFP++; else if (!pred && actual) iFN++; else iTN++;
  }
  const invCM: ConfusionMatrix = { tp: iTP, fp: iFP, tn: iTN, fn: iFN };
  const invTable: CategoryTable = {
    label: "Invariants (positive=Strong)",
    total: withInv.length,
    rows: [
      { name: "Strong", predicted: withInv.filter((r) => r.categories.invariant === "strong").length, oracle: withInv.filter((r) => entryMap.get(r.taskId)!.labels.invariant === "strong").length },
      { name: "Weak/Wrong", predicted: withInv.filter((r) => r.categories.invariant === "weak").length, oracle: withInv.filter((r) => entryMap.get(r.taskId)!.labels.invariant === "weak").length },
      { name: "None (no nodes)", predicted: withInv.filter((r) => r.categories.invariant === "none").length, oracle: 0 },
    ],
    confusionMatrix: invCM, metrics: computeMetrics(invCM),
  };

  return [postTable, preTable, invTable];
}

export function formatCategoryTables(tables: CategoryTable[]): string {
  const lines: string[] = [];
  lines.push("\nPer-Category Results (ProofPulse vs Oracle)");
  lines.push("═".repeat(60));
  for (const t of tables) {
    lines.push(`\n${t.label} (${t.total} entries)`);
    lines.push("─".repeat(60));
    lines.push("  " + "Category".padEnd(22) + "ProofPulse".padStart(12) + "Oracle".padStart(10));
    lines.push("  " + "─".repeat(44));
    for (const row of t.rows) {
      lines.push("  " + row.name.padEnd(22) + String(row.predicted).padStart(12) + String(row.oracle).padStart(10));
    }
    if (t.confusionMatrix && t.metrics) {
      const cm = t.confusionMatrix;
      const m = t.metrics;
      lines.push("");
      lines.push("  Confusion Matrix:");
      lines.push("                   Positive  Negative");
      lines.push(`    Pred Positive   ${String(cm.tp).padStart(6)}    ${String(cm.fp).padStart(6)}`);
      lines.push(`    Pred Negative   ${String(cm.fn).padStart(6)}    ${String(cm.tn).padStart(6)}`);
      lines.push(`  Precision: ${m.precision.toFixed(4)}  Recall: ${m.recall.toFixed(4)}  F1: ${m.f1.toFixed(4)}  Acc: ${m.accuracy.toFixed(4)}`);
    }
  }
  return lines.join("\n");
}

export interface AggregatedDatasetMetrics {
  datasetId: string;
  postconditions: {
    n: number;
    tp: number;
    fp: number;
    fn: number;
    tn: number;
    precision: number;
    recall: number;
    f1: number;
    accuracy: number;
  };
  preconditions: {
    n: number;
    tp: number;
    fp: number;
    fn: number;
    tn: number;
    precision: number;
    recall: number;
    f1: number;
    accuracy: number;
  };
  invariants: {
    n: number;
    tp: number;
    fp: number;
    fn: number;
    tn: number;
    precision: number;
    recall: number;
    f1: number;
    accuracy: number;
  };
}

export function generateAggregateLatexTables(
  allMetrics: AggregatedDatasetMetrics[],
): string {
  const lines: string[] = [];

  // Compute overall totals
  let postTP = 0, postFP = 0, postFN = 0, postTN = 0;
  let preTP = 0, preFP = 0, preFN = 0, preTN = 0;
  let invTP = 0, invFP = 0, invFN = 0, invTN = 0;

  for (const m of allMetrics) {
    postTP += m.postconditions.tp;
    postFP += m.postconditions.fp;
    postFN += m.postconditions.fn;
    postTN += m.postconditions.tn;

    preTP += m.preconditions.tp;
    preFP += m.preconditions.fp;
    preFN += m.preconditions.fn;
    preTN += m.preconditions.tn;

    invTP += m.invariants.tp;
    invFP += m.invariants.fp;
    invFN += m.invariants.fn;
    invTN += m.invariants.tn;
  }

  const postMetrics = computeMetrics({ tp: postTP, fp: postFP, fn: postFN, tn: postTN });
  const preMetrics = computeMetrics({ tp: preTP, fp: preFP, fn: preFN, tn: preTN });
  const invMetrics = computeMetrics({ tp: invTP, fp: invFP, fn: invFN, tn: invTN });

  // Overall Results Table
  lines.push("\\begin{table}[h]");
  lines.push("  \\centering");
  lines.push(
    "  \\caption{ProofPulse classification vs.\\ oracle across all benchmarks. Precision (P), Recall (R), F1, and Accuracy (Acc) are shown per category. For postconditions, oracle=\\textsc{Wrong} entries are excluded from the confusion matrix.}"
  );
  lines.push("  \\label{tab:overall-results}");
  lines.push("  \\begin{tabular}{lrrrrrrr}");
  lines.push("    \\toprule");
  lines.push(
    "    \\textbf{Category} & \\textbf{TP} & \\textbf{FP} & \\textbf{FN} & \\textbf{TN} & \\textbf{P} & \\textbf{R} & \\textbf{Acc} \\\\"
  );
  lines.push("    \\midrule");

  lines.push(
    `    Postconditions & ${postTP} & ${postFP} & ${postFN} & ${postTN} & ${postMetrics.precision.toFixed(2)} & ${postMetrics.recall.toFixed(2)} & ${postMetrics.accuracy.toFixed(2)} \\\\`
  );
  lines.push(
    `    Preconditions  & ${preTP} & ${preFP} & ${preFN} & ${preTN} & ${preMetrics.precision.toFixed(2)} & ${preMetrics.recall.toFixed(2)} & ${preMetrics.accuracy.toFixed(2)} \\\\`
  );
  lines.push(
    `    Invariants     & ${invTP} & ${invFP} & ${invFN} & ${invTN} & ${invMetrics.precision.toFixed(2)} & ${invMetrics.recall.toFixed(2)} & ${invMetrics.accuracy.toFixed(2)} \\\\`
  );

  lines.push("    \\bottomrule");
  lines.push("  \\end{tabular}");
  lines.push("\\end{table}");
  lines.push("");

  // Postconditions Table
  lines.push("\\begin{table}[h]");
  lines.push("  \\centering");
  lines.push("  \\caption{Per-dataset breakdown for postconditions (positive=\\textsc{Strong}).}");
  lines.push("  \\label{tab:postconditions}");
  lines.push("  \\begin{tabular}{lrrrrrrrrr}");
  lines.push("    \\toprule");
  lines.push(
    "    \\textbf{Dataset} & \\textbf{N} & \\textbf{TP} & \\textbf{FP} & \\textbf{FN} & \\textbf{TN} & \\textbf{P} & \\textbf{R}  & \\textbf{F1} & \\textbf{Acc} \\\\"
  );
  lines.push("    \\midrule");
  for (const m of allMetrics) {
    const p = m.postconditions;
    lines.push(
      `    ${m.datasetId}  & ${p.n}  & ${p.tp} & ${p.fp} & ${p.fn} &  ${p.tn} & ${p.precision.toFixed(2)} & ${p.recall.toFixed(2)} & ${p.f1.toFixed(2)} & ${p.accuracy.toFixed(2)} \\\\`
    );
  }
  lines.push("    \\midrule");
  lines.push(
    `    \\textbf{Combined} & \\textbf{${postTP + postFP + postFN + postTN}} & \\textbf{${postTP}} & \\textbf{${postFP}} & \\textbf{${postFN}} & \\textbf{${postTN}} & \\textbf{${postMetrics.precision.toFixed(2)}} & \\textbf{${postMetrics.recall.toFixed(2)}} & \\textbf{${postMetrics.f1.toFixed(2)}} & \\textbf{${postMetrics.accuracy.toFixed(2)}} \\\\`
  );
  lines.push("    \\bottomrule");
  lines.push("  \\end{tabular}");
  lines.push("\\end{table}");
  lines.push("");

  // Preconditions Table
  lines.push("\\begin{table}[h]");
  lines.push("  \\centering");
  lines.push("  \\caption{Per-dataset breakdown for preconditions (positive=\\textsc{Required}).}");
  lines.push("  \\label{tab:preconditions}");
  lines.push("  \\begin{tabular}{lrrrrrrrrr}");
  lines.push("    \\toprule");
  lines.push(
    "    \\textbf{Dataset} & \\textbf{N} & \\textbf{TP} & \\textbf{FP} & \\textbf{FN} & \\textbf{TN} & \\textbf{P} & \\textbf{R}  & \\textbf{F1} & \\textbf{Acc} \\\\"
  );
  lines.push("    \\midrule");
  for (const m of allMetrics) {
    const p = m.preconditions;
    lines.push(
      `    ${m.datasetId}  & ${p.n}  & ${p.tp} & ${p.fp} & ${p.fn} & ${p.tn} & ${p.precision.toFixed(2)} & ${p.recall.toFixed(2)} & ${p.f1.toFixed(2)} & ${p.accuracy.toFixed(2)} \\\\`
    );
  }
  lines.push("    \\midrule");
  lines.push(
    `    \\textbf{Combined} & \\textbf{${preTP + preFP + preFN + preTN}} & \\textbf{${preTP}} & \\textbf{${preFP}} & \\textbf{${preFN}} & \\textbf{${preTN}} & \\textbf{${preMetrics.precision.toFixed(2)}} & \\textbf{${preMetrics.recall.toFixed(2)}} & \\textbf{${preMetrics.f1.toFixed(2)}} & \\textbf{${preMetrics.accuracy.toFixed(2)}} \\\\`
  );
  lines.push("    \\bottomrule");
  lines.push("  \\end{tabular}");
  lines.push("\\end{table}");
  lines.push("");

  // Invariants Table
  lines.push("\\begin{table}[h]");
  lines.push("  \\centering");
  lines.push("  \\caption{Per-dataset breakdown for invariants (positive=\\textsc{Strong}).}");
  lines.push("  \\label{tab:invariants}");
  lines.push("  \\begin{tabular}{lrrrrrrrrr}");
  lines.push("    \\toprule");
  lines.push(
    "    \\textbf{Dataset} & \\textbf{N} & \\textbf{TP} & \\textbf{FP} & \\textbf{FN} & \\textbf{TN} & \\textbf{P} & \\textbf{R}  & \\textbf{F1} & \\textbf{Acc} \\\\"
  );
  lines.push("    \\midrule");
  for (const m of allMetrics) {
    const p = m.invariants;
    lines.push(
      `    ${m.datasetId}  & ${p.n}  & ${p.tp} & ${p.fp} & ${p.fn} & ${p.tn} & ${p.precision.toFixed(2)} & ${p.recall.toFixed(2)} & ${p.f1.toFixed(2)} & ${p.accuracy.toFixed(2)} \\\\`
    );
  }
  lines.push("    \\midrule");
  lines.push(
    `    \\textbf{Combined} & \\textbf{${invTP + invFP + invFN + invTN}} & \\textbf{${invTP}} & \\textbf{${invFP}} & \\textbf{${invFN}} & \\textbf{${invTN}} & \\textbf{${invMetrics.precision.toFixed(2)}} & \\textbf{${invMetrics.recall.toFixed(2)}} & \\textbf{${invMetrics.f1.toFixed(2)}} & \\textbf{${invMetrics.accuracy.toFixed(2)}} \\\\`
  );
  lines.push("    \\bottomrule");
  lines.push("  \\end{tabular}");
  lines.push("\\end{table}");

  return lines.join("\n");
}

export interface ComparisonAggregateDatum {
  datasetId: string;
  total: number;
  overallChanged: number;
  postconditionChanged: number;
  preconditionChanged: number;
  invariantChanged: number;
}

export function generateComparisonAggregateLatexTable(
  data: ComparisonAggregateDatum[],
): string {
  const lines: string[] = [];

  // Compute totals
  let totalN = 0, totalOverall = 0, totalPost = 0, totalPre = 0, totalInv = 0;
  for (const d of data) {
    totalN += d.total;
    totalOverall += d.overallChanged;
    totalPost += d.postconditionChanged;
    totalPre += d.preconditionChanged;
    totalInv += d.invariantChanged;
  }

  // Per-dataset table
  lines.push("\\begin{table}[h]");
  lines.push("  \\centering");
  lines.push("  \\caption{Classification differences (baseline vs.\\ minimized) per verification condition type and dataset.}");
  lines.push("  \\label{tab:minimization-comparison}");
  lines.push("  \\begin{tabular}{lrrrrr}");
  lines.push("    \\toprule");
  lines.push("    \\textbf{Dataset} & \\textbf{N} & \\textbf{Overall} & \\textbf{Post.} & \\textbf{Pre.} & \\textbf{Inv.} \\\\");
  lines.push("    \\midrule");

  for (const d of data) {
    lines.push(
      `    ${d.datasetId} & ${d.total} & ${d.overallChanged} & ${d.postconditionChanged} & ${d.preconditionChanged} & ${d.invariantChanged} \\\\`
    );
  }

  lines.push("    \\midrule");
  lines.push(
    `    \\textbf{Combined} & \\textbf{${totalN}} & \\textbf{${totalOverall}} & \\textbf{${totalPost}} & \\textbf{${totalPre}} & \\textbf{${totalInv}} \\\\`
  );
  lines.push("    \\bottomrule");
  lines.push("  \\end{tabular}");
  lines.push("\\end{table}");

  return lines.join("\n");
}
