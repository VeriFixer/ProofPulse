import * as vscode from "vscode";
import { createDefaultRegistry, SourceLanguage, VerifierBackend } from "@proofpulse/core";

const registry = createDefaultRegistry();
const LANGUAGES: ReadonlySet<string> = new Set(Object.values(SourceLanguage));

/** Backend for a file path (by extension), if ProofPulse supports it. */
export function backendForPath(filePath: string): VerifierBackend | undefined {
  return registry.backendForFile(filePath);
}

/** Backend for an open document: by language id, falling back to the file extension. */
export function backendForDocument(document: vscode.TextDocument): VerifierBackend | undefined {
  const byLanguage = LANGUAGES.has(document.languageId)
    ? registry.backendForLanguage(document.languageId as SourceLanguage)
    : undefined;
  return byLanguage ?? registry.backendForFile(document.fileName);
}

/** "a .dfy" style label of every supported extension, for messages. */
export function supportedExtensionsLabel(): string {
  return registry.fileExtensions().join("/");
}
