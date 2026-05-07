
method DemoImpossiblePrecondition(a: int) returns (r: int)
  requires forall t: int :: t * t + 1 <= t * t
  ensures 2 == 3
{
  var k := a + 1;
  var m := k * 2;
  r := m - k;
}