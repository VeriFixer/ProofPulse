method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a[..] + [b] == c[..]
{
  c := new int[a.Length+1];
  var i:= 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant forall ii::0<= ii <i ==> c[ii]==a[ii] //:: Unused:  _lurking_axioms.dfy(9,15)-(9,49): loop invariant
  {
    c[i] := a[i];
    i:=i+1;
  }
  c[a.Length]:=b;
}


//::: Name - Lurling axioms
//::: Description - invarinat with forall appear not used
//::: L8 - CovComplete