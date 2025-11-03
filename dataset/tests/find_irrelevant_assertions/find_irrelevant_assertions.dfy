method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  assert(43 == 43); 

  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
}

function Id<T> (a : T) : T {
    a
}

//::: Name - Find irrelevant assertions
//::: Description - Assertion on line 5 should be signaled as uncovered . As it is not used in any proof besides itself. 
//::: L1 - CovComplete
//::: L2 - CovTest
//::: L3 - CovTest
//::: L4 - CovComplete
//::: L5 - Uncovered
//::: L6 - CovComplete
//::: L7 - CovComplete
//::: L8 - CovComplete
//::: L9 - CovComplete
//::: L10 - CovComplete
//::: L11 - CovComplete
//::: L12 - Uncovered
//::: L13 - CovComplete
//::: L14 - CovComplete
//::: L15 - CovComplete
//::: L16 - CovComplete
//::: L17 - CovComplete

