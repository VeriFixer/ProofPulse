method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    y := -x;
  } else {
    y := Id(x);
  }
} // This internally is uncovered but now i am ignoring automatic Assertions

function Id<T> (a : T) : T {
    a
}

//::: Name - Find irrelevant assertions
//::: Description - Last char internally is uncovered, as Boogey proves by itself the fact that variable is init at the end of function
//::: L10 - CovTest

// As I am ignoring at the front end is not longer a bug but is here to safe keep
// Internally appears uncovered that line 10 (but was expected CovCompelte)
// But now internally I am making all auto assertions as complete 