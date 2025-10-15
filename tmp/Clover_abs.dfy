method Abs(x: int) returns (y: int)
  ensures x < 0 ==> x+y==0
  ensures x>=0 ==> x==y
{
  if x >= 0 {
    y := x;
  } else {
    y:= -x;
  }
}

// SMT 
// Forma a formula  (x < 0 ==> x+y==0) && ( x>=0 ==> x==y) e tenta negar isso