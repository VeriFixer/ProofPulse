/**
 * Browser entry point: attaches core API to window/global.
 */
import { CovStatus, TokenType } from "./types.js";
import { ProofNode } from "./proof-node.js";
import { Proof, parseProof } from "./proof.js";
import { generateSpansFragment, getDependsOn, getProvedBy, getProves } from "./rendering.js";

const root: Record<string, unknown> =
  typeof window !== "undefined" ? (window as unknown as Record<string, unknown>)
  : typeof global !== "undefined" ? (global as unknown as Record<string, unknown>)
  : {};

root.CovStatus = CovStatus;
root.TokenType = TokenType;

root.sampleLog = "";
root.sourceCode = "";
root.targetFileName = "";

root.parseProof = function (dafnyCode: string, proofLog: string): Proof {
  root.sampleLog = proofLog;
  root.sourceCode = dafnyCode;
  return parseProof(dafnyCode, proofLog);
};

root.generateSpansFragment = function (code: string, proof: Proof): string {
  return generateSpansFragment(code, proof.proofGraph);
};

root.getDependsOn = function (key: string, proof: Proof): unknown {
  return getDependsOn(key, proof.proofGraph);
};

root.getProvedBy = function (key: string, proof: Proof): unknown {
  return getProvedBy(key, proof.proofGraph);
};

root.getProves = function (key: string, proof: Proof): unknown {
  return getProves(key, proof.proofGraph);
};

root.getUsageCount = function (key: string, proof: Proof): number {
  return proof.proofGraph.getUsageCount(key);
};

root.getMethodContexts = function (key: string, proof: Proof): string[] {
  return proof.proofGraph.getMethodContexts(key);
};

root.getConnections = function (key: string, proof: Proof): { node: ProofNode; depth: number }[] {
  return proof.proofGraph.getConnections(key).map(n => ({ node: n, depth: 1 }));
};

root.getCalledBy = function (key: string, proof: Proof): { node: ProofNode; depth: number }[] {
  return proof.proofGraph.getCalledBy(key).map(n => ({ node: n, depth: 1 }));
};

root.getSampleLog = function (): unknown {
  return root.sampleLog;
};

root.getSourceCode = function (): unknown {
  return root.sourceCode;
};
