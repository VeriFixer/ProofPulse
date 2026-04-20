import type { ClassificationResult } from "./classifier.js";

export interface ConfusionMatrix {
  tp: number; // predicted strong, oracle strong
  fp: number; // predicted strong, oracle weak
  tn: number; // predicted weak, oracle weak
  fn: number; // predicted weak, oracle strong
}

export interface Metrics {
  precision: number;
  recall: number;
  f1: number;
  accuracy: number;
}

export function computeConfusionMatrix(
  results: ClassificationResult[]
): ConfusionMatrix {
  const filtered = results.filter((r) => r.classification !== "error");
  let tp = 0,
    fp = 0,
    tn = 0,
    fn = 0;
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
  const f1 =
    precision + recall === 0
      ? 0
      : (2 * precision * recall) / (precision + recall);
  const total = tp + fp + tn + fn;
  const accuracy = total === 0 ? 0 : (tp + tn) / total;
  return { precision, recall, f1, accuracy };
}

export function formatTable(cm: ConfusionMatrix, metrics: Metrics): string {
  const lines: string[] = [];
  lines.push("Confusion Matrix");
  lines.push("─────────────────────────────────");
  lines.push("                 Oracle Strong  Oracle Weak");
  lines.push(
    `  Pred Strong     ${String(cm.tp).padStart(5)}          ${String(cm.fp).padStart(5)}`
  );
  lines.push(
    `  Pred Weak       ${String(cm.fn).padStart(5)}          ${String(cm.tn).padStart(5)}`
  );
  lines.push("");
  lines.push("Metrics");
  lines.push("─────────────────────────────────");
  lines.push(`  Precision:  ${metrics.precision.toFixed(4)}`);
  lines.push(`  Recall:     ${metrics.recall.toFixed(4)}`);
  lines.push(`  F1:         ${metrics.f1.toFixed(4)}`);
  lines.push(`  Accuracy:   ${metrics.accuracy.toFixed(4)}`);
  return lines.join("\n");
}
