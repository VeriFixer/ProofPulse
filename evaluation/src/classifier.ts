import { type NodeData, TokenType, CovStatus } from "@proofpulse/core";

export interface ClassificationResult {
  taskId: string;
  filePath: string;
  classification: "strong" | "weak" | "error";
  oracleLabel: "strong" | "weak";
  postconditionLines: number[];
  bodyLines: number[];
  coverageStatuses: Record<number, CovStatus>;
  error?: string;
}

export function classifySpec(nodes: NodeData[]): "strong" | "weak" {
  const postconditions = nodes.filter(
    (n) => n.type === TokenType.Postcondition
  );
  const bodyNodes = nodes.filter((n) => n.type === TokenType.CodeLine);

  if (postconditions.length === 0) return "weak";

  const allPostconditionsCovered = postconditions.every(
    (n) =>
      n.covStatus === CovStatus.CovComplete ||
      n.covStatus === CovStatus.CovTest
  );
  if (!allPostconditionsCovered) return "weak";

  const allBodyComplete = bodyNodes.every(
    (n) => n.covStatus === CovStatus.CovComplete
  );
  if (!allBodyComplete) return "weak";

  return "strong";
}
