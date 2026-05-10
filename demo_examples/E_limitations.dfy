method BugAssignmentCoverage(x: int) returns (y: int)
  ensures x >= 0 ==> x == y
  ensures x < 0 ==> x + y == 0
{
  if x < 0 {
    y := -x;
  } else {
    y := x; // Direct assigments appear always uncovered
  }
}

// Forall and exist can give false reports
// allocators, modifies can give false reports
