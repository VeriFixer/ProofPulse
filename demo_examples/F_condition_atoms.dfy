// Condition coverage: which parts of an if/while condition the proof needs.
// An Uncovered part can be replaced by any boolean (true, false, anything)
// and the method still verifies: it decides behaviour the contract leaves open.
// Needs the ProofPulse Dafny build with condition atom tracking.

// 1. Tie-break: any index of a maximum satisfies the contract.
method IndexOfMax(a: seq<int>) returns (best: nat)
  requires |a| > 0
  ensures best < |a| && forall j :: 0 <= j < |a| ==> a[j] <= a[best]
{
  best := 0;
  var k := 1;
  while k < |a|                                              // needed
    invariant 1 <= k <= |a| && best < |a|
    invariant forall j :: 0 <= j < k ==> a[j] <= a[best]
  {
    if a[k] > a[best] || (a[k] == a[best] && k % 2 == 0) {  // `k % 2 == 0` unused
      best := k;
    }
    k := k + 1;
  }
}

// 2. Weak contract: nothing fixes the sign of r, so the test is unused.
method Abs(x: int) returns (r: int)
  ensures r * r == x * x
{
  if x < 0 { r := -x; } else { r := x; }  // `x < 0` unused: add `ensures r >= 0`
}

// 3. Same code, full contract: the test is needed.
method AbsFull(x: int) returns (r: int)
  ensures r >= 0 && r * r == x * x
{
  if x < 0 { r := -x; } else { r := x; }  // `x < 0` needed
}

// 4. One extra conjunct: it only decides which occurrence of x is returned.
method Find(a: seq<int>, x: int) returns (i: int)
  requires x in a
  ensures 0 <= i < |a| && a[i] == x
{
  i := 0;
  while !(a[i] == x)  // needed
    invariant 0 <= i < |a| && x in a[i..]
    decreases |a| - i
  {
    i := i + 1;
  }
  if i + 1 < |a| && a[i + 1] == x && i % 3 == 0 {  // `i % 3 == 0` unused
    i := i + 1;
  }
}

// 5. Defensive check: the atom is needed (the else branch would break the
// postcondition), but that branch is dead, so it shows as uncovered code.
method Div(a: int, b: int) returns (q: int)
  requires b > 0
  ensures q == a / b
{
  if b != 0 { q := a / b; } else { q := 0; }  // `q := 0` uncovered
}

// 6. A weak specification found in the wild (MBPP-style task): the
// postcondition does not define the median, so none of the tests is needed.
method MedianOfThree(a: int, b: int, c: int) returns (median: int)
  ensures median == a || median == b || median == c
{
  if (a <= b && b <= c) || (c <= b && b <= a) {
    median := b;
  } else if (b <= a && a <= c) || (c <= a && a <= b) {
    median := a;
  } else {
    median := c;
  }
}

// 7. While loop with an extra stop condition: the contract only bounds the
// result, so when the loop stops early is left open.
method CountUp(n: nat) returns (i: nat)
  ensures i <= n
{
  i := 0;
  while i < n && i != 7  // `i < n` needed, `i != 7` unused
    invariant i <= n
  {
    i := i + 1;
  }
}

// 8. Same loop, exact contract: the guard is needed.
method CountUpFull(n: nat) returns (i: nat)
  ensures i == n
{
  i := 0;
  while i < n  // needed
    invariant i <= n
  {
    i := i + 1;
  }
}

// 9. else-if chain: both tests are needed, but the contract says nothing
// about x == 0, so the last branch is uncovered code.
method Sign(x: int) returns (s: int)
  ensures x > 0 ==> s == 1
  ensures x < 0 ==> s == -1
{
  if x > 0 {          // needed
    s := 1;
  } else if x < 0 {   // needed
    s := -1;
  } else {
    s := 0;           // uncovered
  }
}

// 10. Nested loops: the inner loop only moves j, which the contract never
// mentions, so `j := 0` is uncovered. Its guard is still needed: Dafny must
// prove the inner loop terminates (decreases i - j), and that uses `j < i`.
method Outer(n: nat) returns (i: nat)
  ensures i == n
{
  i := 0;
  while i < n  // needed
    invariant i <= n
  {
    var j := 0;    // uncovered
    while j < i  // needed (termination)
    {
      j := j + 1;
    }
    i := i + 1;
  }
}
