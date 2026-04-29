// ProofPulse demo: Verus-to-Dafny translation of a Fibonacci/power proof.
// This version keeps the original proof structure but uses Dafny syntax and ghost lemmas.

function pow(base: nat, exp: nat): nat
  decreases exp
{
  if exp == 0 then 1 else base * pow(base, exp - 1)
}

function fib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 1 else fib(n - 1) + fib(n - 2)
}

lemma PowMonotonic(base: nat, n: nat, k: nat)
  requires 1 <= base
  requires n <= k
  ensures pow(base, n) <= pow(base, k)
  decreases k
{
  if k == 0 {
  } else if n == k {
  } else {
    assert n <= k - 1;
    PowMonotonic(base, n, k - 1);
    assert pow(base, k) == base * pow(base, k - 1);
    assert pow(base, k - 1) <= pow(base, k);
  }
}

lemma PowStep(base: nat, k: nat)
  requires 1 <= base
  ensures pow(base, k) <= pow(base, k + 1)
{
  assert pow(base, k + 1) == base * pow(base, k);
}

lemma FibMonotonic(n: nat, k: nat)
  requires n <= k
  ensures fib(n) <= fib(k)
  decreases k
{
  if k == 0 {
    assert n == 0;
  } else if k == 1 {
    assert n == 0 || n == 1;
  } else {
    if n == k {
    } else {
      assert n <= k - 1;
      FibMonotonic(n, k - 1);
      assert fib(k - 1) <= fib(k);
    }
  }
}

lemma FibBoundByPow2(n: nat)
  ensures fib(n) <= pow(2, n)
  decreases n
{
  if n == 0 || n == 1 {
  } else {
    FibMonotonic(n - 2, n - 1);
    FibBoundByPow2(n - 1);
    assert fib(n) == fib(n - 1) + fib(n - 2);
    assert fib(n - 2) <= fib(n - 1);
    assert fib(n) <= fib(n - 1) + fib(n - 1);
    assert fib(n) <= 2 * fib(n - 1);
    assert fib(n - 1) <= pow(2, n - 1);
    assert 2 * fib(n - 1) <= 2 * pow(2, n - 1);
    PowStep(2, n - 1);
    assert 2 * pow(2, n - 1) == pow(2, n);
    assert fib(n) <= pow(2, n);
  }
}

lemma Pow2LessThanU64Max()
  ensures pow(2, 63) < 18446744073709551615


method ComputeFib(n: nat) returns (finb: nat)
  requires 0 < n <= 63
  ensures finb == fib(n)
  ensures finb <= pow(2, 63)
{
  if n == 1 {
    //Pow2LessThanU64Max();
    PowMonotonic(2, 0, 63);
    assert pow(2, 0) == 1;
    assert 1 <= pow(2, 63);
    finb := 1;
    return;
  }

  var acc1 := 1;
  var acc2 := 1;
  var idx := 1;

  while idx < n
    invariant 1 <= idx <= n
    invariant n <= 63
    invariant acc1 == fib(idx)
    invariant acc2 == fib(idx - 1)
    invariant fib(idx - 1) <= pow(2, idx - 1)
    invariant fib(idx) <= pow(2, idx)
    decreases n - idx
  {
    //FibBoundByPow2(idx);
    //FibBoundByPow2(idx - 1);
    PowMonotonic(2, idx, 63);

    var save := acc1;
    acc1 := acc2 + acc1;
    acc2 := save;
    idx := idx + 1;
  }

  assert idx == n;
  assert acc1 == fib(n);
  FibBoundByPow2(n);
  PowMonotonic(2, n, 63);
  finb := acc1;
}

method Main()
{
  var r := ComputeFib(3);
  assert r == 3;
}
