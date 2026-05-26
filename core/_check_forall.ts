import { parseProof } from './src/index.js';
import { runDafny } from './src/dafny-runner.js';
import { TokenType, CovStatus } from './src/types.js';
import * as fs from 'fs';

const filePath = '../dataset/tests/test_forall_needs_merging/test_forall_needs_merging.dfy';
const src = fs.readFileSync(filePath, 'utf-8');

async function main() {
  const result = await runDafny(filePath, {
    dafnyPath: '/home/ricostynha/Desktop/proof_pulse_custom_dafny_boogie/dafny_proofpulse/Binaries/Dafny',
    timeoutSeconds: 60,
  });
  
  // Show raw log
  console.log('=== RAW PROOF LOG (first 200 lines) ===');
  const logLines = result.log.split('\n');
  for (let i = 0; i < Math.min(200, logLines.length); i++) {
    console.log(logLines[i]);
  }
  
  console.log('\n=== PARSED NODES ===');
  const proof = parseProof(src, result.log);
  const allNodes = proof.proofGraph.getAllNodes();
  
  // Show all nodes on line 3 (the forall postcondition)
  console.log('\nNodes on line 3:');
  for (const n of allNodes) {
    if (n.start.line === 3) {
      console.log(`  ${n.id} [${n.type}] "${n.prooftext}" cov=${n.covStatus} isTop=${n.isTopAssertion} method=${n.methodName} check=${n.checkType}`);
    }
  }
  
  // Show all uncovered nodes
  console.log('\nAll Uncovered nodes:');
  for (const n of allNodes) {
    if (n.covStatus === CovStatus.Uncovered) {
      console.log(`  ${n.id} [${n.type}] "${n.prooftext}" isTop=${n.isTopAssertion} check=${n.checkType}`);
    }
  }
}

main().catch(console.error);
