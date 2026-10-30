// Contradictory preconditions: the postcondition holds vacuously.
method IncVacuous(x: int) returns (y: int)
  requires x > 0
  requires x < 0
  ensures y > x
{
  y := x - 1;
}

// Same method without the contradiction: an ordinary proof.
method IncOk(x: int) returns (y: int)
  requires x > 0
  ensures y > x
{
  y := x + 1;
}

// `assume` with a false condition: everything after it is vacuous.
method AssumeFalse(x: int) returns (y: int)
  ensures y == x + 1
{
  assume {:axiom} x != x;
  y := 0;
}

// Dead branch: the assertion inside it is proved vacuously.
method DeadBranch(x: int) returns (y: int)
  requires x > 0
  ensures y >= 0
{
  if x < 0 {
    assert x > 100;
    y := -1;
  } else {
    y := x;
  }
}

// Proof by contradiction: the branch is impossible and `assert false` says so.
lemma MaxIsUpperBound(x: int, y: int, m: int)
  requires m == (if x > y then x else y)
  ensures m >= x && m >= y
{
  if m < x || m < y {
    assert false;
  }
}

// Proof by contradiction with an intermediate step: `{:contradiction}` marks it as intended.
lemma AbsNonNegative(x: int, a: int)
  requires a == (if x < 0 then -x else x)
  ensures a >= 0
{
  if a < 0 {
    assert {:contradiction} a >= 0;
  }
}

//::: Name - Vacuous proofs are flagged, proofs by contradiction are not
//::: Description - Contradictory requires/assume make goal, contradiction and unreachable code Vacuous; a dead-branch assert is Vacuous; assert false and {:contradiction} keep their normal status
//::: L1 - CovComplete
//::: L2 - CovComplete
//::: L3 - Vacuous
//::: L4 - Vacuous
//::: L5 - Vacuous
//::: L6 - CovComplete
//::: L7 - Vacuous
//::: L8 - Vacuous
//::: L9 - CovComplete
//::: L10 - CovComplete
//::: L11 - CovComplete
//::: L12 - Uncovered
//::: L13 - CovTest
//::: L14 - CovComplete
//::: L15 - CovComplete
//::: L16 - CovComplete
//::: L17 - CovComplete
//::: L18 - CovComplete
//::: L19 - CovComplete
//::: L20 - Vacuous
//::: L21 - CovComplete
//::: L22 - Vacuous
//::: L23 - Vacuous
//::: L24 - Vacuous
//::: L25 - CovComplete
//::: L26 - CovComplete
//::: L27 - CovComplete
//::: L28 - CovComplete
//::: L29 - CovTest
//::: L30 - CovComplete
//::: L31 - CovComplete
//::: L32 - Vacuous
//::: L33 - Uncovered
//::: L34 - CovComplete
//::: L35 - CovComplete
//::: L36 - CovComplete
//::: L37 - CovComplete
//::: L38 - CovComplete
//::: L39 - CovComplete
//::: L40 - CovComplete
//::: L41 - CovComplete
//::: L42 - CovTest
//::: L43 - CovComplete
//::: L44 - CovComplete
//::: L45 - CovComplete
//::: L46 - CovComplete
//::: L47 - CovComplete
//::: L48 - CovComplete
//::: L49 - CovComplete
//::: L50 - CovComplete
//::: L51 - CovComplete
//::: L52 - CovTest
//::: L53 - CovComplete
//::: L54 - CovComplete
//::: L55 - CovComplete
//::: L56 - CovComplete
//::: L57 - CovComplete
//::: L58 - CovComplete
