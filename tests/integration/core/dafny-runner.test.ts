import { afterEach, describe, expect, it, vi } from "vitest";
import { chmod, mkdir, rm, writeFile } from "node:fs/promises";
import { dirname, join } from "node:path";
import { tmpdir } from "node:os";
import { resolveDafnyPathWithSource, resolveZ3PathWithSource } from "../../../core/src/dafny-runner.js";

async function createExecutable(filePath: string): Promise<void> {
  await mkdir(dirname(filePath), { recursive: true });
  await writeFile(filePath, "#!/bin/sh\n", "utf8");
  await chmod(filePath, 0o755);
}

describe("Dafny runner path resolution", () => {
  afterEach(() => {
    vi.unstubAllEnvs();
  });

  it("resolves dafny and z3 from PATH when available", async () => {
    const root = join(tmpdir(), `proofpulse-path-${Date.now()}`);

    try {
      const dafnyBin = join(root, "bin", "dafny");
      const z3Bin = join(root, "bin", "z3");

      await createExecutable(dafnyBin);
      await createExecutable(z3Bin);

      vi.stubEnv("PATH", join(root, "bin"));
      // Prevent bundled VS Code extension lookup from taking priority
      vi.stubEnv("HOME", join(root, "fakehome"));

      expect(resolveDafnyPathWithSource("dafny")?.path).toBe(dafnyBin);
      expect(resolveZ3PathWithSource(dafnyBin)?.path).toBe(z3Bin);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("keeps explicit Dafny paths unchanged", () => {
    expect(resolveDafnyPathWithSource("/opt/dafny/dafny")).toEqual({ path: "/opt/dafny/dafny", source: "manual" });
  });
});