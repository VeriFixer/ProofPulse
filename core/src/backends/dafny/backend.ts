import { readFile } from "node:fs/promises";
import {
  BackendCapabilities,
  BackendOptions,
  BackendRun,
  RunStatus,
  SourceLanguage,
  ToolInfo,
  VerifierBackend,
} from "../backend.js";
import { VerifierId } from "../../report/coverage-report.js";
import { DafnyMinimizationHook } from "./minimization-hook.js";
import { DafnyRunResult, DEFAULT_DAFNY_COMMAND, probeVersion, resolveDafnyPathWithSource, runDafny } from "./runner.js";
import { dafnyLogToReport } from "./log-parser.js";

/** Convert a raw Dafny run into a backend result with a coverage report. */
export function dafnyRunToBackendRun(result: DafnyRunResult, minimized: boolean, sourceText?: string): BackendRun {
  const base = {
    status: result.status,
    rawLog: result.log,
    exitCode: result.exitCode,
    ...(result.errorMessage !== undefined ? { errorMessage: result.errorMessage } : {}),
  };
  if (result.status !== RunStatus.Completed) return base;
  try {
    return { ...base, report: dafnyLogToReport(result.log, { version: result.dafnyVersion, minimized, sourceText }) };
  } catch (err) {
    return { ...base, status: RunStatus.Failed, errorMessage: `could not read Dafny log: ${(err as Error).message}` };
  }
}

export class DafnyBackend implements VerifierBackend {
  readonly id = VerifierId.Dafny;
  readonly displayName = "Dafny";
  readonly fileExtensions = [".dfy"] as const;
  readonly languages = [SourceLanguage.Dafny] as const;
  readonly capabilities: BackendCapabilities = { proofDependencies: true, callTargets: true, progressive: true };
  readonly minimizationHook = new DafnyMinimizationHook();

  async probe(opts: BackendOptions = {}): Promise<ToolInfo | undefined> {
    const resolved = resolveDafnyPathWithSource(opts.toolPath ?? DEFAULT_DAFNY_COMMAND);
    if (!resolved) return undefined;
    const version = probeVersion(resolved.path, "--version") ?? probeVersion(resolved.path, "/version");
    return { path: resolved.path, ...(version ? { version } : {}) };
  }

  async run(file: string, opts: BackendOptions = {}): Promise<BackendRun> {
    const { onPreliminaryResult, ...rest } = opts;
    // Read before verifying so the text matches the log's spans.
    const sourceText = await readFile(file, "utf-8").catch(() => undefined);
    const result = await runDafny(file, {
      ...rest,
      ...(onPreliminaryResult ? { onPreliminaryResult: (r: DafnyRunResult) => onPreliminaryResult(dafnyRunToBackendRun(r, false, sourceText)) } : {}),
    });
    return dafnyRunToBackendRun(result, opts.minimization !== undefined, sourceText);
  }
}
