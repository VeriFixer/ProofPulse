import { CovStatus, TokenType, SourceLocation, NodeData } from "./types.js";

export class Node {
  id: string;
  file: string;
  start: SourceLocation;
  end: SourceLocation;
  prooftext: string;
  isTopAssertion: boolean;
  covStatus: CovStatus;
  covStatusInternal: CovStatus;
  type: TokenType;
  proves: Set<Node>;
  provedBy: Set<Node>;

  constructor(
    file: string,
    sLine: number,
    sCol: number,
    eLine: number,
    eCol: number,
    prooftext: string,
    isTopAssertion: boolean,
  ) {
    this.file = file;
    this.prooftext = prooftext;
    this.start = { line: sLine, col: sCol };
    this.end = { line: eLine, col: eCol };

    this.isTopAssertion = isTopAssertion;

    this.covStatus = CovStatus.Uncovered;
    this.covStatusInternal = CovStatus.Uncovered;

    this.type = TokenType.Undefined;

    this.id = `${this.file}:${this.start.line},${this.start.col}-${this.end.line},${this.end.col}`;

    this.proves = new Set();
    this.provedBy = new Set();

    this.updateIsTopAssertion(isTopAssertion);
  }

  updateIsTopAssertion(isTopAssertion: boolean): void {
    this.isTopAssertion = isTopAssertion;
    if (this.prooftext.includes("this postcondition holds")) {
      this.type = TokenType.Postcondition;
    } else if (this.prooftext.includes("precondition always holds")) {
      this.type = TokenType.Precondition;
    } else if (this.prooftext.includes("ensures clause at")) {
      this.type = TokenType.Call;
    } else if (this.prooftext.includes("requires clause at")) {
      this.type = TokenType.Call;
    } else if (this.prooftext.includes("ensures clause")) {
      this.type = TokenType.Postcondition;
    } else if (this.prooftext.includes("requires clause")) {
      this.type = TokenType.Precondition;
    } else if (this.prooftext.includes("assertion always holds")) {
      this.type = TokenType.AssertionManual;
    } else if (
      this.prooftext.includes("index in range") ||
      this.prooftext.includes("target object is never null") ||
      this.prooftext.includes("which is subject to definite-assignment rules, is always initialized at this return point") ||
      this.prooftext.includes("which is subject to definite-assignment rules, is always initialized here") || 
      this.prooftext.includes("decreases expression is bounded below by") ||
      this.prooftext.includes("value always satisfies the subset constraints of") || 
      this.prooftext.includes("an array element is in the enclosing context's modifies clause") || 
      this.prooftext.includes("sufficient reads clause to read array element") 
    ) {
      this.type = TokenType.AssertionAutomatic;
    } else if (this.isTopAssertion) {
      this.type = TokenType.AssertionAutomatic;
    } else {
      this.type = TokenType.CodeLine;
    }
  }

  connectTo(target: Node): void {
    this.provedBy.add(target);
    target.proves.add(this);
  }

  toJSON(): NodeData {
    return {
      id: this.id,
      file: this.file,
      start: { ...this.start },
      end: { ...this.end },
      prooftext: this.prooftext,
      isTopAssertion: this.isTopAssertion,
      type: this.type,
      covStatus: this.covStatus,
      covStatusInternal: this.covStatusInternal,
    };
  }

  static fromJSON(data: NodeData): Node {
    const node = new Node(
      data.file,
      data.start.line,
      data.start.col,
      data.end.line,
      data.end.col,
      data.prooftext,
      data.isTopAssertion,
    );
    node.type = data.type;
    node.covStatus = data.covStatus;
    node.covStatusInternal = data.covStatusInternal;
    return node;
  }
}
