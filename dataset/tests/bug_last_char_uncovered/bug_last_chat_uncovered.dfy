method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
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
//::: L10 - CovComplete