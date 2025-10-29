  ghost predicate prime(n: nat)
{ n > 1 && (forall nr | 1 < nr < n :: n % nr != 0) }

  method testPrimeness(n: nat) returns (result: bool) 
      ensures result <==> prime(n)
  {
   if n == 0 || n == 1{
    return false;
   }
    var i := 2;
    result := true;

    while i < n 
      invariant i >= 2 && i <= n //:: UNUSED   _compound_assertion.dfy(15,17)-(15,32): loop invariant
      invariant result <==> (forall j |  1 < j <= i - 1 :: n % j != 0)
    {
      if n % i == 0 {
        result := false; 
      }
      i := i + 1;
    }
  }

//:: Note invariant is signalized as unused but only part of it is really unsed
//:: If commented out verification fails! (but if only i>=2 commented out it passes)
//:: However proof dependency report is signaliing complete assertion!

  method testPrimeness2(n: nat) returns (result: bool) 
      ensures result <==> prime(n)
  {
   if n == 0 || n == 1{
    return false;
   }
    var i := 2;
    result := true;

    while i < n 
      invariant i <= n //:: This line is signalling as unused even though it is being used
      invariant result <==> (forall j |  1 < j <= i - 1 :: n % j != 0)
    {
      if n % i == 0 {
        result := false; 
      }
      i := i + 1;
    }
  }

  //:: Maybe something related with the lurking axiom?