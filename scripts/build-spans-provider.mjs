#!/usr/bin/env node
/**
 * Bundles @proofpulse/core browser-entry into src/spans_provider.js (IIFE).
 * Replaces the old hand-written spans_provider.js with one backed by core.
 */
import * as esbuild from "esbuild";

await esbuild.build({
  entryPoints: ["packages/core/src/browser-entry.ts"],
  bundle: true,
  format: "iife",
  outfile: "src/spans_provider.js",
  platform: "browser",
  target: "es2020",
  // Exclude node-only modules that core imports but browser-entry doesn't use
  external: ["node:child_process", "node:fs/promises", "node:path", "node:os"],
});

console.log("Built src/spans_provider.js from @proofpulse/core");
