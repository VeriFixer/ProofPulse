method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x==-y
{
  if x < 0 {
    y := -x;
  } else {
    y :=  x;
  }
}