// ProofPulse demo showcase
// This file groups several minimal examples in one place for live demos.

function IdDemo<T>(a: T): T {
  a
}

// 1) Simple example where things work as expected.
method DemoSimpleWorking(a: int) returns (x: int)
  ensures x == 32
{
  x := 32;
}

// 2) Redundant code line: the assignment in the first branch is irrelevant to the proof.
method DemoRedundantLine(x: int) returns (y: int)
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> x + y == 0
{
  if x == 0 {
    y := 0; // Redundant for the final proof obligations in this method.
  }

  if x < 0 {
    y := -x;
  } else {
    y := IdDemo(x);
  }
}

// 3) No contracts: code lines are expected to be signaled as not contributing to contracts.
method DemoNoContracts(x: int) returns (y: int)
{
  var tmp := x + 1;
  y := tmp - 1;
}

// 4) Specification line not using code: the first ensures is trivially true.
method DemoSpecNotUsingCode(x: int) returns (y: int)
  ensures 4 == 4
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> x + y == 0
{
  if x < 0 {
    y := -x;
  } else {
    y := IdDemo(x);
  }
}

// 5) irrelevant assertion (self-justified specification).
method DemoIrrelevantAssertion(x: int) returns (y: int)
  ensures y == x
{
  assert 43 == 43;
  y := IdDemo(x);
}

// 6) Vacuous proof example: contradictory postcondition under impossible precondition.
// The precondition is false, but encoded as a quantified arithmetic statement.
method DemoImpossiblePrecondition(a: int) returns (r: int)
  requires forall t: int :: t * t + 1 <= t * t
  ensures 2 == 3
{
  var k := a + 1;
  var m := k * 2;
  r := m - k;
}

// 7) Postcondition reuse across call site (good contract consumption).
method AddOneDemo(x: int) returns (y: int)
  ensures y == x + 1
{
  y := x + 1;
}

method DemoPostconditionReuse()
{
  var a := AddOneDemo(41);
  assert a == 42;
}

// 8) Boundary-safe indexing with explicit precondition.
method DemoBoundarySafeRead(a: array<int>, i: int) returns (v: int)
  requires 0 <= i < a.Length
  ensures v == a[i]
{
  v := a[i];
}

// 9) Loop invariant that is truly useful to prove the final postcondition.
method DemoLoopInvariantUseful(n: int) returns (s: int)
  requires n >= 0
  ensures s == n
{
  var i := 0;
  s := 0;
  while i < n
    invariant 0 <= i 
    invariant i <= n
    invariant s == i
  {
    s := s + 1;
    i := i + 1;
  }
}

// 10) Strong helper contract reused by multiple callers/assertions.
method ClampNonNegativeDemo(x: int) returns (y: int)
  ensures y >= 0
  ensures x >= 0 ==> y == x
{
  if x < 0 {
    y := 0;
  } else {
    y := IdDemo(x);
  }
}

method DemoContractChainUse()
{
  var z := ClampNonNegativeDemo(-5);
  assert z >= 0;

  var w := ClampNonNegativeDemo(7);
  assert w == 7;
}

// 11) Assertion that is aligned with code and postcondition (useful assertion).
method DemoUsefulAssertion(x: int) returns (y: int)
  ensures y >= x
{
  y := IdDemo(x);
  assert y >= x; // This highlights problem of core minimality, prove passes without this assertion
}

// 12) Contract exists but is not needed by caller (caller ignores returned value).
method ProducerWithStrongContract(x: int) returns (y: int)
  ensures y == x + 10
{
  y := x + 10;
}

method DemoUnusedContractAtCallSite_IgnoreResult()
{
  var tmp := ProducerWithStrongContract(5);
  var keep := 1;
  keep := keep + 1;
}

// 13) Contract exists but caller proves goal without using callee contract.
method ProducerNonNegative(x: int) returns (y: int)
  ensures y >= 0
{
  if x < 0 {
    y := 0;
  } else {
    y := IdDemo(x);
  }
}

method DemoUnusedContractAtCallSite_IndependentProof()
{
  var t := ProducerNonNegative(-100); // No constraint or t is made so previous contract not used
  assert 1 + 1 == 2; // Assertion is not used to anything
}


// -----------------------------------------------------------------------------
//  Potentially by exclusion can be made to give hints to user in debugging failure proofs
// -----------------------------------------------------------------------------
datatype Point = Point(x: int, y: int)
datatype Rectangle = Rectangle(p1: Point, p2: Point)

predicate ValidRectangle(r: Rectangle) {
  r.p1.x <= r.p2.x && r.p1.y <= r.p2.y &&  0 < r.p1.x < 1 && 0 < r.p1.y < 1 && 0 < r.p2.x < 1 && 0 < r.p2.y < 1
}

predicate PointInsideRectangle(p: Point, r: Rectangle) {
  r.p1.x <= p.x <= r.p2.x &&
  r.p1.y <= p.y <= r.p2.y
}

ghost predicate RectangleIntersect(r1: Rectangle, r2: Rectangle) {
  exists p: Point :: PointInsideRectangle(p, r1) && PointInsideRectangle(p, r2)
}

function Max(a: int, b: int): int {
  if a >= b then a else b
}

method BugLurkingAxiomsRectangleWitness(r1: Rectangle, r2: Rectangle) returns (out: bool)
  requires ValidRectangle(r1) 
  requires ValidRectangle(r2)
  ensures out == RectangleIntersect(r1, r2)
{
  if r1.p2.x < r2.p1.x || r2.p2.x < r1.p1.x {
    out := false;
    return;
  }

  if r1.p2.y < r2.p1.y || r2.p2.y < r1.p1.y {
    out := false;
    return;
  }

  //ghost var witX := Max(r1.p1.x, r2.p1.x);
  //ghost var witY := Max(r1.p1.y, r2.p1.y);
  //ghost var wit := Point(witX, witY);

  //assert PointInsideRectangle(wit, r1);
  //assert PointInsideRectangle(wit, r2);

  //assert RectangleIntersect(r1, r2);
  out := true;
}
