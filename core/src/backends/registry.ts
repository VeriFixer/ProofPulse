import { extname } from "node:path";
import type { SourceLanguage, VerifierBackend } from "./backend.js";
import type { VerifierId } from "../report/coverage-report.js";
import { DafnyBackend } from "./dafny/backend.js";

/** Maps files and languages to the verifier backend that handles them. */
export class BackendRegistry {
  private readonly backends = new Map<VerifierId, VerifierBackend>();

  register(backend: VerifierBackend): this {
    this.backends.set(backend.id, backend);
    return this;
  }

  get(id: VerifierId): VerifierBackend | undefined {
    return this.backends.get(id);
  }

  all(): VerifierBackend[] {
    return Array.from(this.backends.values());
  }

  /** All file extensions some backend handles (e.g. [".dfy"]). */
  fileExtensions(): string[] {
    return Array.from(new Set(this.all().flatMap((b) => b.fileExtensions)));
  }

  /**
   * Backend for a file, by extension. When several backends claim the
   * extension (Verus and Kani both take `.rs`), `preferred` decides, else the
   * first one registered.
   */
  backendForFile(path: string, preferred?: VerifierId): VerifierBackend | undefined {
    const ext = extname(path).toLowerCase();
    return this.pick(this.all().filter((b) => b.fileExtensions.includes(ext)), preferred);
  }

  backendForLanguage(language: SourceLanguage, preferred?: VerifierId): VerifierBackend | undefined {
    return this.pick(this.all().filter((b) => b.languages.includes(language)), preferred);
  }

  private pick(candidates: VerifierBackend[], preferred?: VerifierId): VerifierBackend | undefined {
    return candidates.find((b) => b.id === preferred) ?? candidates[0];
  }
}

/** Registry with every backend ProofPulse ships (Dafny today). */
export function createDefaultRegistry(): BackendRegistry {
  return new BackendRegistry().register(new DafnyBackend());
}
