import { defineConfig } from "vitest/config";
import path from "path";

export default defineConfig({
  resolve: {
    alias: {
      "@proofpulse/core": path.resolve(__dirname, "../packages/core/src/index.ts"),
    },
  },
  test: {
    root: __dirname,
    include: ["src/**/*.test.ts"],
  },
});
