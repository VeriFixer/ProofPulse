import { defineConfig } from "vitest/config";
import path from "path";

export default defineConfig({
  resolve: {
    alias: {
      "@proofpulse/core": path.resolve(__dirname, "core/src/index.ts"),
    },
  },
  test: {
    root: __dirname,
    include: ["tests/**/*.test.ts"],
    exclude: [
      "**/node_modules/**",
    ],
  },
});
