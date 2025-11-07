method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if(x == 0){
    y := 0; // Unused by proof  _USECASE_find_irrelevant_lines.dfy(6,5)-(6,11): assignment (or return)
  }

  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
}

function Id<T> (a : T) : T {
    a
}

//::: Name - Find irrelevant lines (not used in proofs)
//::: Description - Line 6 is not used in any proof and should be marked as uncovered, safe to be removed
//::: L1 - CovComplete
//::: L2 - CovTest
//::: L3 - CovTest
//::: L4 - CovComplete
//::: L5 - CovComplete
//::: L6 - Uncovered
//::: L7 - CovComplete
//::: L8 - CovComplete
//::: L9 - CovComplete
//::: L10 - CovComplete
//::: L11 - CovComplete
//::: L12 - CovComplete
//::: L13 - CovComplete
//::: L14 - CovComplete
//::: L15 - CovComplete
//::: L16 - CovComplete
//::: L17 - CovComplete

