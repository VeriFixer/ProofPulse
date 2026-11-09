/** Environment variables the z3 minimizer wrapper reads. */
export enum Z3WrapperEnv {
  SolverPath = "PROOFPULSE_Z3_PATH",
  LogFile = "PROOFPULSE_WRAPPER_LOG",
  Mode = "PROOFPULSE_WRAPPER_MODE",
  /** "0" skips reading z3's trace for facts that supplied trigger terms. */
  TriggerTrace = "PROOFPULSE_TRIGGER_TRACE",
}

/** What the wrapper does with each unsat core. */
export enum Z3WrapperMode {
  /** Make sure the core proves the goal on its own. */
  Check = "check",
  /** Check, then minimize (the default). */
  Minimize = "minimize",
}
