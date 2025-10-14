method Abs(x: int) returns (y: int)
  ensures x>=0 ==> x==y
  ensures x<0 ==> x+y==0
{
  if x < 0 {
    assert(x < 0);
    y := -x;
    assert x + y == 0;
    assert (x < 0 ==> x+y==0);
    return y;

  } else {
    assert(x >= 0);
    y := x;
    assert(x == y);
    assert(x>=0 ==> x==y);
    return y;
  }
}


method test_abs(){
  var a := Abs(-7);
  assert(7 == a);
  var b := Abs(7);
  assert(7 == b);

}