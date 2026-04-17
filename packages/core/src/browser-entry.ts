/**
 * Browser entry point: attaches core API to window/global
 * so the web viewer (app.js) can use it the same way as the old spans_provider.js.
 */
import { CovStatus, TokenType } from "./types.js";
import { Proof, parseProof } from "./proof.js";
import { generateSpansFragment, getDependsOn } from "./rendering.js";

const root: Record<string, unknown> =
  typeof window !== "undefined" ? (window as unknown as Record<string, unknown>)
  : typeof global !== "undefined" ? (global as unknown as Record<string, unknown>)
  : {};

root.CovStatus = CovStatus;
root.TokenType = TokenType;

root.sampleLog = "";
root.sourceCode = "";
root.targetFileName = "_USECASE_find_irrelevant_lines_for_proof.dfy";

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

root.getSampleLog = function (): unknown {
  return root.sampleLog;
};

root.getSourceCode = function (): unknown {
  return root.sourceCode;
};
