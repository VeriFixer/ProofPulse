method Abs(x: int) returns (y: int)
  ensures 4 == 4
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    y := -x; // _USECASE_no_postconditions.dfy(4,5)-(4,12): assignment (or return)
  } else {
    y :=  Id(x); // _USECASE_no_postconditions.dfy(6,5)-(6,11): assignment (or return)
  }
}

function Id<T> (a : T) : T {
    a
}

//::: Name - Find irrelevant postconditions that are not used in the code not needed
//::: Description - Line 2 should be uncovered as ensures 4==4 does not use anything in the code to prove it
//::: L1 - CovComplete
//::: L2 - Uncovered
//::: L3 - CovTest
//::: L4 - CovTest
//::: L5 - CovComplete
//::: L6 - CovComplete
//::: L7 - CovComplete
//::: L8 - CovComplete
//::: L9 - CovComplete
//::: L10 - CovComplete
//::: L11 - CovComplete
//::: L12 - CovComplete
//::: L13 - CovComplete
//::: L14 - CovComplete
//::: L15 - CovComplete

