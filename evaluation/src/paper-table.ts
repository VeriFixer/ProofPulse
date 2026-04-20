/**
 * Reproduces the paper's Table showing manual evaluation breakdown
 * for all RQ datasets (3 prompts × 2 models).
 *
 * Usage: npx tsx evaluation/src/paper-table.ts --repo-root dafny-synthesis
 */
import * as path from "node:path";
import { parseAllOracles, ALL_DATASETS, type DatasetId } from "./oracle-parser.js";

const repoRoot = process.argv.includes("--repo-root")
  ? process.argv[process.argv.indexOf("--repo-root") + 1]
  : "dafny-synthesis";

const allOracles = parseAllOracles(path.resolve(repoRoot));

console.log("Paper Table Reproduction: Manual Evaluation Results");
console.log("═".repeat(70));

for (const ds of ALL_DATASETS) {
  const entries = allOracles.get(ds.id as DatasetId) ?? [];
  if (entries.length === 0) {
    console.log(`\n${ds.id}: (no verified entries with postcondition tags)`);
    continue;
  }

  const withPost = entries.filter((e) => e.labels.postcondition != null);
  const postStrong = withPost.filter((e) => e.labels.postcondition === "strong").length;
  const postWeak = withPost.filter((e) => e.labels.postcondition === "weak").length;
  const postWrong = withPost.filter((e) => e.labels.postcondition === "wrong").length;

  const withInv = entries.filter((e) => e.labels.invariant != null);
  const invStrong = withInv.filter((e) => e.labels.invariant === "strong").length;
  const invWeak = withInv.filter((e) => e.labels.invariant === "weak").length;

  const withPre = entries.filter((e) => e.labels.precondition != null);
  const preRequired = withPre.filter((e) => e.labels.precondition === "required").length;
  const preOptional = withPre.filter((e) => e.labels.precondition === "optional").length;

  console.log(`\n${"─".repeat(70)}`);
  console.log(`${ds.id} (verified with post tag: ${entries.length})`);
  console.log(`${"─".repeat(70)}`);
  console.log(`  Postconditions:  Strong ${postStrong}/${withPost.length}  |  Weak ${postWeak}/${withPost.length}  |  Wrong ${postWrong}/${withPost.length}`);
  if (withInv.length > 0)
    console.log(`  Invariants:      Strong ${invStrong}/${withInv.length}  |  Weak/Wrong ${invWeak}/${withInv.length}`);
  if (withPre.length > 0)
    console.log(`  Preconditions:   Required ${preRequired}/${withPre.length}  |  Optional ${preOptional}/${withPre.length}`);
}

console.log(`\n${"═".repeat(70)}`);
console.log("\nPaper reference (Dynamic Few-Shot GPT-4):");
console.log("  Post: Strong 103/114, Weak 3/114, Wrong 8/114");
console.log("  Inv:  Strong 51/57, Weak/Wrong 6/57");
console.log("  Pre:  Required 36/74, Optional 38/74");
