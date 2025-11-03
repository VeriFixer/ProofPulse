method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    y := -x;
  } else {
    y := x; // Line never covered bug report opened
  }
}

//::: Name - Bug assigment never covered
//::: Description - assigment line is never covered bug report already opened for Boogie team
//::: L8 - CovComplete