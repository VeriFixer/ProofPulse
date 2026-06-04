import * as vscode from "vscode";
import * as path from "path";
import * as fs from "fs";
import * as https from "https";
import * as http from "http";
import { execSync } from "child_process";

/** GitHub release zip URL for each platform */
const RELEASE_URLS: Record<string, string> = {
  "linux-x64": "https://github.com/VeriFixer/dafny_proofpulse/releases/download/v0.1.0-proofpulse/dafny-0.1.0-proofpulse-x64-ubuntu-22.04.zip",
  "darwin-arm64": "https://github.com/VeriFixer/dafny_proofpulse/releases/download/v0.1.0-proofpulse/dafny-0.1.0-proofpulse-arm64-macos-14.zip",
  "win32-x64": "https://github.com/VeriFixer/dafny_proofpulse/releases/download/v0.1.0-proofpulse/dafny-0.1.0-proofpulse-x64-windows-2022.zip",
};

function getPlatformKey(): string | undefined {
  const platform = process.platform;
  const arch = process.arch;
  if (platform === "linux" && arch === "x64") return "linux-x64";
  if (platform === "darwin" && arch === "arm64") return "darwin-arm64";
  if (platform === "win32" && arch === "x64") return "win32-x64";
  return undefined;
}

/** Where we install Dafny inside the extension's globalStorage */
export function getInstallDir(context: vscode.ExtensionContext): string {
  return path.join(context.globalStorageUri.fsPath, "dafny-proofpulse");
}

/** Path to the dafny binary inside our managed install */
export function getBundledDafnyPath(context: vscode.ExtensionContext): string {
  const bin = process.platform === "win32" ? "dafny.exe" : "dafny";
  return path.join(getInstallDir(context), "dafny", bin);
}

/** Check if bundled Dafny is already installed and executable */
export function isBundledInstalled(context: vscode.ExtensionContext): boolean {
  const bin = getBundledDafnyPath(context);
  try {
    fs.accessSync(bin, fs.constants.X_OK);
    return true;
  } catch {
    return false;
  }
}

/** Returns true if we need to install (bundled is the default, skip if custom enabled or already installed) */
export function needsInstall(context: vscode.ExtensionContext): boolean {
  const useCustom = vscode.workspace.getConfiguration("proofpulse").get<boolean>("useCustomDafny", false);
  if (useCustom) return false;
  if (isBundledInstalled(context)) return false;
  return true;
}

/** Download file following redirects, with progress callback (0-100) */
function downloadWithProgress(
  url: string,
  onProgress: (percent: number) => void,
): Promise<Buffer> {
  return new Promise((resolve, reject) => {
    const doRequest = (reqUrl: string, redirects = 0) => {
      if (redirects > 10) { reject(new Error("Too many redirects")); return; }
      const mod = reqUrl.startsWith("https") ? https : http;
      mod.get(reqUrl, { headers: { "User-Agent": "ProofPulse-VSCode" } }, (res) => {
        if (res.statusCode && res.statusCode >= 300 && res.statusCode < 400 && res.headers.location) {
          doRequest(res.headers.location, redirects + 1);
          return;
        }
        if (res.statusCode !== 200) {
          reject(new Error(`Download failed: HTTP ${res.statusCode}`));
          return;
        }
        const totalBytes = parseInt(res.headers["content-length"] || "0", 10);
        let receivedBytes = 0;
        const chunks: Buffer[] = [];
        res.on("data", (chunk: Buffer) => {
          chunks.push(chunk);
          receivedBytes += chunk.length;
          if (totalBytes > 0) {
            onProgress(Math.round((receivedBytes / totalBytes) * 100));
          }
        });
        res.on("end", () => resolve(Buffer.concat(chunks)));
        res.on("error", reject);
      }).on("error", reject);
    };
    doRequest(url);
  });
}

/** Install ProofPulse Dafny to extension globalStorage */
export async function installDafny(context: vscode.ExtensionContext): Promise<string | undefined> {
  const platformKey = getPlatformKey();
  if (!platformKey) {
    const action = await vscode.window.showWarningMessage(
      `ProofPulse: No pre-built Dafny for ${process.platform}-${process.arch}. Enable "Use Custom Dafny" in settings and provide your own binary.`,
      "Open Settings"
    );
    if (action === "Open Settings") {
      vscode.commands.executeCommand("workbench.action.openSettings", "proofpulse.useCustomDafny");
    }
    return undefined;
  }

  const url = RELEASE_URLS[platformKey];
  if (!url) return undefined;

  const installDir = getInstallDir(context);
  const zipPath = path.join(installDir, "dafny.zip");

  return vscode.window.withProgress(
    {
      location: vscode.ProgressLocation.Notification,
      title: "ProofPulse",
      cancellable: false,
    },
    async (progress) => {
      try {
        fs.mkdirSync(installDir, { recursive: true });

        // Download with percentage
        progress.report({ message: "Downloading Dafny (ProofPulse build)… 0%", increment: 0 });
        let lastPercent = 0;
        const data = await downloadWithProgress(url, (percent) => {
          const delta = percent - lastPercent;
          if (delta > 0) {
            progress.report({ message: `Downloading Dafny (ProofPulse build)… ${percent}%`, increment: delta * 0.8 });
            lastPercent = percent;
          }
        });

        // Write zip
        fs.writeFileSync(zipPath, data);

        // Extract
        progress.report({ message: "Extracting Dafny…", increment: 10 });
        if (process.platform === "win32") {
          execSync(
            `powershell -NoProfile -Command "Expand-Archive -Force -Path '${zipPath}' -DestinationPath '${installDir}'"`,
            { stdio: "ignore" }
          );
        } else {
          try {
            execSync(`unzip -qo "${zipPath}" -d "${installDir}"`, { stdio: "ignore" });
          } catch {
            execSync(
              `python3 -c "import zipfile; zipfile.ZipFile('${zipPath}').extractall('${installDir}')"`,
              { stdio: "ignore" }
            );
          }
        }

        // Cleanup
        fs.unlinkSync(zipPath);

        // Ensure executable (not needed on Windows)
        const bin = getBundledDafnyPath(context);
        if (process.platform !== "win32") {
          fs.chmodSync(bin, 0o755);
        }

        progress.report({ message: "Dafny ready ✓", increment: 10 });
        vscode.window.showInformationMessage("ProofPulse: Custom Dafny 4.11.1 installed and ready.");
        return bin;
      } catch (err: unknown) {
        const msg = err instanceof Error ? err.message : String(err);
        vscode.window.showErrorMessage(`ProofPulse: Failed to install Dafny — ${msg}`);
        try { fs.rmSync(installDir, { recursive: true, force: true }); } catch { /* ignore */ }
        return undefined;
      }
    }
  );
}
