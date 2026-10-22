import YAML from "js-yaml";
import type { CoverageReport } from "./coverage-report.js";
import { validateCoverageReport } from "./validate.js";

export enum ReportFormat {
  Yaml = "yaml",
  Json = "json",
}

/** Pick the format from a file name (`.json` → JSON, anything else → YAML). */
export function reportFormatForPath(path: string): ReportFormat {
  return path.toLowerCase().endsWith(".json") ? ReportFormat.Json : ReportFormat.Yaml;
}

/** Parse a YAML or JSON string (JSON is valid YAML) and validate it. */
export function parseCoverageReport(text: string): CoverageReport {
  return validateCoverageReport(YAML.load(text));
}

export function serializeCoverageReport(report: CoverageReport, format: ReportFormat = ReportFormat.Yaml): string {
  // Drop undefined optional fields so YAML and JSON carry the same content.
  const plain = JSON.parse(JSON.stringify(report));
  return format === ReportFormat.Json ? JSON.stringify(plain, null, 2) + "\n" : YAML.dump(plain, { noRefs: true });
}
