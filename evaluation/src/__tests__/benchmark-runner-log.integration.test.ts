import { describe, it, expect } from "vitest";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { buildLogPath } from "../agent-helpers.js";

describe("benchmark-runner log integration", () => {
  it("buildLogPath produces correct path for a real filename and directory can be created", () => {
    const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "pp-log-test-"));

    try {
      const dataset = "RQ1-GPT4";
      const filename = "task_id_126.dfy";

      // Write a minimal .dfy file
      const dfyContent = "method Foo() ensures true {}\n";
      const dfyPath = path.join(tmpDir, filename);
      fs.writeFileSync(dfyPath, dfyContent);

      // Verify buildLogPath produces correct format
      const logPath = buildLogPath(dataset, filename);
      expect(logPath).toBe(".eval-tmp/logs/RQ1-GPT4/task_id_126.log.txt");

      // Verify we can create the directory structure for the log path
      const fullLogDir = path.join(tmpDir, path.dirname(logPath));
      fs.mkdirSync(fullLogDir, { recursive: true });
      expect(fs.existsSync(fullLogDir)).toBe(true);

      // Verify we can write a log file there
      const fullLogPath = path.join(tmpDir, logPath);
      fs.writeFileSync(fullLogPath, "test log content");
      expect(fs.readFileSync(fullLogPath, "utf-8")).toBe("test log content");
    } finally {
      fs.rmSync(tmpDir, { recursive: true, force: true });
    }
  });
});
