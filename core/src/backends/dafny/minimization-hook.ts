import { SolverKind } from "../../report/coverage-report.js";
import type { MinimizationHook, MinimizerCommand } from "../backend.js";

/** Dafny/Boogie spawn whatever `--solver-path` names as their z3. */
export class DafnyMinimizationHook implements MinimizationHook {
  readonly supportedSolvers = [SolverKind.Z3] as const;

  apply(cmd: MinimizerCommand): { args: string[]; env: Record<string, string> } {
    return { args: ["--solver-path", cmd.executable], env: cmd.env };
  }
}
