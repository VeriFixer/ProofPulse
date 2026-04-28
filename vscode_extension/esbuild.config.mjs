import * as esbuild from "esbuild";
import { cpSync, mkdirSync, writeFileSync } from "node:fs";
import { resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = dirname(fileURLToPath(import.meta.url));
const watch = process.argv.includes("--watch");

/** @type {import('esbuild').BuildOptions} */
const extensionConfig = {
  entryPoints: ["src/extension.ts"],
  bundle: true,
  outfile: "dist/extension.js",
  external: ["vscode"],
  format: "cjs",
  platform: "node",
  target: "es2022",
  sourcemap: true,
};

/**
 * Bundle web_viewer/server.js so it runs standalone with all deps inlined.
 * Keep ESM format (server.js uses top-level await + import.meta.url).
 * Inject __dirname shim so dafny-runner.ts code works.
 */
/** @type {import('esbuild').BuildOptions} */
const serverConfig = {
  entryPoints: [resolve(__dirname, "..", "web_viewer", "server.js")],
  bundle: true,
  outfile: "dist/web_viewer/server.js",
  format: "esm",
  platform: "node",
  target: "es2022",
  sourcemap: true,
  banner: {
    js: [
      'import { createRequire as __createRequire } from "node:module";',
      'import { dirname as __banner_dirname } from "node:path";',
      'import { fileURLToPath as __banner_fileURLToPath } from "node:url";',
      'const __filename = __banner_fileURLToPath(import.meta.url);',
      'const __dirname = __banner_dirname(__filename);',
    ].join("\n"),
  },
};

/** Copy static web_viewer assets + core scripts into dist/ */
function copyAssets() {
  const webSrc = resolve(__dirname, "..", "web_viewer");
  const webDest = resolve(__dirname, "dist", "web_viewer");
  mkdirSync(webDest, { recursive: true });
  for (const file of ["index.html", "styles.css", "app.js", "spans_provider.js"]) {
    cpSync(resolve(webSrc, file), resolve(webDest, file));
  }

  // Declare ESM so Node doesn't warn about module type
  writeFileSync(resolve(webDest, "package.json"), '{"type":"module"}\n');

  // core/scripts/ — dafny-runner resolves via resolve(__dirname, '..', 'scripts')
  // extension.js: __dirname=dist/ → needs <ext>/scripts/
  // server.js:    __dirname=dist/web_viewer/ → needs dist/scripts/
  const scriptsSrc = resolve(__dirname, "..", "core", "scripts");

  // Single copy at dist/scripts/ — both extension.js and server.js resolve here
  const scriptsDist = resolve(__dirname, "dist", "scripts");
  mkdirSync(scriptsDist, { recursive: true });
  cpSync(scriptsSrc, scriptsDist, { recursive: true });
}

if (watch) {
  const ctx = await esbuild.context(extensionConfig);
  await ctx.watch();
  console.log("Watching...");
} else {
  await esbuild.build(extensionConfig);
  await esbuild.build(serverConfig);
  copyAssets();
  console.log("Build complete.");
}
