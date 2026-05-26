import { CovStatus, TokenType, SourceLocation, NodeData } from "./types.js";


export class Node {
  file: string;
  start: SourceLocation;
  end: SourceLocation;
  prooftext: string;
  assertion_group: string;
  methodType: string;
  isTopAssertion: boolean;

  private _id: string;
  covStatus: CovStatus;
  covStatusInternal: CovStatus;
  type: TokenType;

  constructor(
    file: string,
    sLine: number,
    sCol: number,
    eLine: number,
    eCol: number,
    prooftext: string,
    assertion_group: string,
    isTopAssertion: boolean = false,
    methodType: string = ""
  ) {
    this.file = file;
    this.prooftext = prooftext;
    this.start = { line: sLine, col: sCol };
    this.end = { line: eLine, col: eCol };
    this.assertion_group = assertion_group;
    this.methodType = methodType;
    this.isTopAssertion = isTopAssertion;

    this.covStatus = CovStatus.Uncovered;
    this.covStatusInternal = CovStatus.Uncovered;
    this.type = classifyNodeType(this.prooftext, this.isTopAssertion);

    const normalizeForId = (s: string) =>
      s
        .replace(/\s+/g, " ")
        .replace(/\|/g, "/")
        .trim();

    const methodName = normalizeForId(this.assertion_group || "");
    const methodTypeNorm = normalizeForId(this.methodType || "");
    const span = `${this.start.line},${this.start.col}-${this.end.line},${this.end.col}`;
    const assertionType = this.type;
    this._id = `${this.file}|${methodName}|${methodTypeNorm}|${span}|${assertionType}`;
  }

  get id(): string {
    return this._id;
  }

  getId(): string {
    return this._id;
  }

  getType(): TokenType {
    return this.type;
  }

  getCovStatus(): CovStatus {
    return this.covStatus;
  }

  setCovStatus(s: CovStatus): void {
    this.covStatus = s;
  }

  getCovStatusInternal(): CovStatus {
    return this.covStatusInternal;
  }

  setCovStatusInternal(s: CovStatus): void {
    this.covStatusInternal = s;
  }
}

export class CallNode extends Node {
  connections: Set<Node> = new Set();

  addConnection(node: Node): boolean {
    const before = this.connections.size;
    this.connections.add(node);
    return this.connections.size !== before;
  }
}

export class TopNode extends Node {
  connections: Set<Node>;
  provedBy: Set<Node>;
  proofUnused: Set<Node>;

  constructor(
    file: string,
    sLine: number,
    sCol: number,
    eLine: number,
    eCol: number,
    prooftext: string,
    assertion_group: string,
    methodType: string = "",
  ) {
    super(
      file, sLine, sCol, eLine, eCol, prooftext, assertion_group, true, methodType
    );

    this.connections = new Set();
    this.provedBy = new Set();
    this.proofUnused = new Set();
  }
}

export function classifyNodeType(prooftext: string, isTopAssertion: boolean): TokenType {
  if (prooftext.includes("this postcondition holds")) {
    return TokenType.Postcondition;
  } else if (prooftext.includes("precondition always holds")) {
    return TokenType.Precondition;
  } else if (prooftext.includes("ensures clause at")) {
    return TokenType.Call;
  } else if (prooftext.includes("requires clause at")) {
    return TokenType.Call;
  } else if (prooftext.includes("ensures clause")) {
    return TokenType.Postcondition;
  } else if (prooftext.includes("requires clause")) {
    return TokenType.Precondition;
  } else if (prooftext.includes("assertion always holds")) {
    return TokenType.AssertionManual;
  } else if (
    prooftext.includes("loop invariant holds on entry") ||
    prooftext.includes("loop invariant is maintained by the loop") ||
    prooftext.includes("loop invariant always holds") ||
    prooftext === "loop invariant"
  ) {
    return TokenType.LoopInvariant;
  } else if (
    prooftext.includes("index in range") ||
    prooftext.includes("target object is never null") ||
    prooftext.includes("array is never null") ||
    prooftext.includes("which is subject to definite-assignment rules, is always initialized at this return point") ||
    prooftext.includes("which is subject to definite-assignment rules, is always initialized here") ||
    prooftext.includes("decreases expression is bounded below by") ||
    prooftext.includes("value always satisfies the subset constraints of") ||
    prooftext.includes("an array element is in the enclosing context's modifies clause") ||
    prooftext.includes("sufficient reads clause to read array element")
  ) {
    return TokenType.AssertionAutomatic;
  } else if (isTopAssertion) {
    return TokenType.AssertionAutomatic;
  } else {
    return TokenType.CodeLine;
  }
}
