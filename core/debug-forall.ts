import { parseProof } from "./src/proof.js";
import { runDafny } from "./src/dafny-runner.js";
import * as fs from "fs";

async function main() {
  const src = fs.readFileSync("/home/ricostynha/Desktop/ProofPulse/dataset/tests/test_forall_needs_merging/test_forall_needs_merging.dfy", "utf-8");
  const result = await runDafny("/home/ricostynha/Desktop/ProofPulse/dataset/tests/test_forall_needs_merging/test_forall_needs_merging.dfy");
  if (result.error) { console.error(result.error); return; }

  const proof = parseProof(src, result.log);

  console.log("=== ALL NODES AT LINE 3 ===");
  const allNodes = proof.proofGraph.getAllNodes();
  const line3 = allNodes.filter(n => n.start.line === 3);
  for (const n of line3) {
    console.log(`  ${n.id} | type=${n.type} | covStatus=${n.covStatus} | isTop=${n.isTopAssertion} | text="${n.prooftext}"`);
    console.log(`    proves: [${[...n.proves].map(p => p.id).join(", ")}]`);
    console.log(`    provedBy: [${[...n.provedBy].map(p => p.id).join(", ")}]`);
  }
}

main();
