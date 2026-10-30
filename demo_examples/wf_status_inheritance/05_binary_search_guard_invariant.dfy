method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i,j :: 0 <= i < j <a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i :: 0<= i < n ==> a[i] < key
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> a[i] < key
  ensures forall i :: n<= i < a.Length ==> a[i]>=key
{
  // In the same line did not worked, separated and with did solved
  // TODO find why
  //var lo, hi := 0, a.Length; 
  var lo := 0; //Clover_binary_search.dfy(8,7)-(8,28): assignment (or return) 
  var hi := a.Length;  //Clover_binary_search.dfy(8,7)-(8,28): assignment (or return)

  while lo < hi
    invariant 0 <= lo <= hi <= a.Length 
    invariant forall i :: 0 <= i < lo ==> a[i] < key  // Clover_binary_search.dfy(11,15)-(11,46): loop invariant (not solved try lurking)
    invariant forall i :: hi <= i <a.Length ==> a[i] >= key // Clover_binary_search.dfy(13,15)-(13,57): loop invariant (not solved try lurking)
  {
    var mid := (lo + hi) / 2;
    if a[mid] < key {
      lo := mid + 1;
    } else {
      hi := id(mid); //Clover_binary_search.dfy(19,7)-(19,16): assignment (or return)  (solved with trick id)
    }
  }
  n:=id(lo); //Clover_binary_search.dfy(22,3)-(22,8): assignment (or return) (solved with trick id)
}

function id(x:int) : int {
  x
}

//:: Expected

//:: with id() and separating in two lines simultaneous assigments, only missing invariants with forall
//:: possibly lurking axioms there!

// Well formness not used
    // Unused by proof:
    //   Clover_binary_search.dfy(2,46)-(2,55): method requires clause
    //   Clover_binary_search.dfy(2,26)-(2,55): method requires clause
    //   Clover_binary_search.dfy(2,12)-(2,55): method requires clause
    //   Clover_binary_search.dfy(4,37)-(4,44): method ensures clause
    //   Clover_binary_search.dfy(4,23)-(4,44): method ensures clause
    //   Clover_binary_search.dfy(4,11)-(4,44): method ensures clause
    //   Clover_binary_search.dfy(5,11)-(5,18): method ensures clause
    //   Clover_binary_search.dfy(5,63)-(5,70): method ensures clause
    //   Clover_binary_search.dfy(5,41)-(5,70): method ensures clause
    //   Clover_binary_search.dfy(5,29)-(5,70): method ensures clause
    //   Clover_binary_search.dfy(5,11)-(5,70): method ensures clause
    //   Clover_binary_search.dfy(6,44)-(6,50): method ensures clause
    //   Clover_binary_search.dfy(6,23)-(6,50): method ensures clause
    //   Clover_binary_search.dfy(6,11)-(6,50): method ensures clause



// Code not used
    // Unused by proof:
    //   Clover_binary_search.dfy(8,7)-(8,28): assignment (or return)
    //   Clover_binary_search.dfy(8,7)-(8,28): assignment (or return)
    //   Clover_binary_search.dfy(11,15)-(11,46): loop invariant
    //   Clover_binary_search.dfy(12,15)-(12,54): loop invariant
    //   Clover_binary_search.dfy(18,7)-(18,16): assignment (or return)
    //   Clover_binary_search.dfy(21,3)-(21,8): assignment (or return)

