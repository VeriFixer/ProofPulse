import { defineConfig } from "vitest/config";
import path from "path";

export default defineConfig({
  resolve: {
    alias: {
      "@proofpulse/core": path.resolve(__dirname, "../core/src/index.ts"),
    },
  },
  test: {
    root: path.resolve(__dirname, ".."),
    include: [
      "tests/unit/evaluation/**/*.test.ts",
      "tests/property/evaluation/**/*.test.ts",
      "tests/integration/evaluation/**/*.test.ts",
    ],
  },
});
