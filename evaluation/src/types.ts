/**
 * Closed value sets used by the evaluation. Enum values equal the strings
 * written to JSON / LaTeX / markdown outputs, so serialized data is unchanged.
 */
import { assertNever } from "@proofpulse/core";

/** Strength of a postcondition / invariant set as classified by ProofPulse. */
export enum SpecStrength {
  Strong = "strong",
  Weak = "weak",
  /** No (correctness) nodes of this category. */
  None = "none",
}

/** Whether a method's preconditions are needed, as classified by ProofPulse. */
export enum PreconditionNeed {
  Required = "required",
  Optional = "optional",
  /** No (correctness) preconditions. */
  None = "none",
}

/** Overall per-file classification. */
export enum Classification {
  Strong = "strong",
  Weak = "weak",
  /** Dafny failed / timed out, or the analysis threw. */
  Error = "error",
}

/** Manual (oracle) label of a file's postconditions. */
export enum OracleLabel {
  Strong = "strong",
  Weak = "weak",
  Wrong = "wrong",
}

/** Direction of a divergence between ProofPulse and the oracle. */
export enum ErrorDirection {
  FalsePositive = "FP",
  FalseNegative = "FN",
}

/** Specification category a divergence refers to. */
export enum SpecCategory {
  Postcondition = "postcondition",
  Precondition = "precondition",
  Invariant = "invariant",
}

/** Root cause assigned to a divergence by the classification agent. */
export enum RootCause {
  QuantifierNotTracked = "quantifier_not_tracked",
  TriviallyTrueSpec = "trivially_true_spec",
  OracleError = "oracle_error",
  MultiMethod = "multi_method",
  ToolLimitation = "tool_limitation",
  InsufficientCoverageModel = "insufficient_coverage_model",
  Other = "other",
}

/** True when ProofPulse's overall classification equals the oracle label. */
export function classificationMatchesOracle(classification: Classification, oracle: OracleLabel): boolean {
  switch (classification) {
    case Classification.Strong: return oracle === OracleLabel.Strong;
    case Classification.Weak: return oracle === OracleLabel.Weak;
    case Classification.Error: return false;
    default: return assertNever(classification);
  }
}
