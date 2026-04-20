export interface InteractiveStep {
  filePath: string;
  coverageJson: object;
  classification: "strong" | "weak" | "error";
  oracleLabel: "strong" | "weak";
  pass: boolean;
}

export function formatInteractiveOutput(step: InteractiveStep): string {
  const lines = [
    `Running proof_coverage on file ${step.filePath}...`,
    `Obtained the following coverage JSON: ${JSON.stringify(step.coverageJson, null, 2)}`,
    `Classification: ${step.classification}`,
    `Oracle classification: ${step.oracleLabel}`,
    step.pass ? "PASS" : "FAIL",
  ];
  return lines.join("\n");
}

export async function printInteractiveStep(
  step: InteractiveStep
): Promise<void> {
  console.log(formatInteractiveOutput(step));
  await waitForKeypress();
}

export async function waitForKeypress(): Promise<void> {
  console.log("[Press any key to continue]");
  return new Promise<void>((resolve) => {
    const wasRaw = process.stdin.isRaw;
    process.stdin.setRawMode(true);
    process.stdin.resume();
    process.stdin.once("data", () => {
      process.stdin.setRawMode(wasRaw ?? false);
      process.stdin.pause();
      resolve();
    });
  });
}
