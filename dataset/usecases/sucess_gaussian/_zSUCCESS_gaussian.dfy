// VERIFY USING DAFNY:
// /Applications/dafny/dafny /Users/apple/GaussianDP/Dafny/gaussian.dfy
method gaussian (size:int, q: array<real>, q_hat: array<real>) returns (out: array<real>)
  requires q_hat.Length==size
  requires q.Length==size
  requires size > 0
  requires arraySquaredSum(q_hat[..]) <= 1.0
{
  var i : int := 0;
  // This values being initialized to zero were not being used in any proof!
  var alpha : real := arraySquaredSum(q_hat[..1]); //:: gaussian.dfy(10,20)-(10,50): assignment (or return)
  //var eta: real := 0.0; //:: FOUND initialized to zero was not being used in a proof gaussian.dfy(11,17)-(11,23): assignment (or return)
  //var eta_hat: real := 0.0; //:: FOUND initialized to zero gaussian.dfy(12,21)-(12,27): assignment (or return)
  var eta: real;
  var eta_hat :real;

  out := new real[size];//:: gaussian.dfy(13,3)-(13,24): assignment (or return)
  while (i <size)
    invariant 0 < i <= size ==> alpha <= arraySquaredSum(q_hat[..i]) //:: Not understand why this is not being used gaussian.dfy(15,15)-(15,68): loop invariant
    invariant i<=size //:: Not understand why this is not being used gaussian.dfy(16,15)-(16,18): loop invariant
  {
    eta := *;
    eta_hat := - q_hat[i];
    alpha := arraySquaredSum(q_hat[..i+1]);
    //assert (q_hat[i] + eta_hat ==0.0);
    out[i] := q[i] + eta; //:: FOUND BUG gaussian.dfy(16,15)-(16,18): loop invariant (this line really is not needed on proofs! it is missing proofs for that)
    i := i+1;
  }
  //assert i==size;
  assert alpha <= arraySquaredSum(q_hat[..size]); //:: FOUND REDUNDANT gaussian.dfy(26,10)-(26,48): assert statement
  assert q_hat[..size] == q_hat[..];
  assert alpha <= arraySquaredSum(q_hat[..]); //:: FOUND REDUNDANT gaussian.dfy(28,10)-(28,44): assert statement
  assert alpha <= 1.0;
}


function arraySquaredSum(a: seq<real>): real
  requires |a| > 0
{
  if |a| == 1 then
    a[0]*a[0]
  else
    (a[0]*a[0]) + arraySquaredSum(a[1..])
}