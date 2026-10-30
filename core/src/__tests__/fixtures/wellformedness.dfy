function sum(s: seq<int>, n: int): int
  requires 0 <= n <= |s|
{
  if n == 0 then 0 else sum(s, n - 1) + s[n - 1]
}

// A guard that makes a covered ensures well-defined: covered.
method Get(a: array<int>, i: int) returns (x: int)
  requires 0 <= i < a.Length
  ensures x == a[i]
{
  x := a[i];
}

method UseGet(a: array<int>) returns (y: int)
  requires a.Length > 0
  ensures y == a[0]
{
  y := Get(a, 0);
}

// A lemma no one calls: its ensures is CovTest, but what makes it well-defined is covered, like what proves it.
lemma SumStep(s: seq<int>, n: int)
  requires 0 <= n < |s|
  ensures sum(s, n + 1) == sum(s, n) + s[n]
{
}

// An invariant that only makes an uncovered invariant well-defined: both uncovered.
method Total(s: seq<int>) returns (t: int)
{
  t := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant t == sum(s, i)
  {
    t := t + s[i];
    i := i + 1;
  }
}

// A lemma call is held by its call: what its precondition needs gets the call's status.
lemma {:axiom} Distinct(s: set<int>, t: set<int>)
  requires s < t
  ensures |s| < |t|

method Grow(s: set<int>, x: int) returns (t: set<int>)
  requires x !in s
{
  t := s + {x};
  Distinct(s, t);
  assert |s| < |t|;
}
