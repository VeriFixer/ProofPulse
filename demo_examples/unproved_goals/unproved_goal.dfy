method Unproved(x: int, y: int) returns (r: int)
  requires x > 0
  requires y > 0
  ensures r >= 0
  ensures r > x
{
  var z := 3;
  r := x + y - 1;
}

method Sum(a: int, b: int) returns (s: int)
  ensures s == a + b
{
  var unused := 7;
  s := a + b;
}
