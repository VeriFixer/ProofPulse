method append(a:array<int>, b:int) returns (c:array<int>)
  requires a.Length > 0
  ensures a.Length == c.Length
  ensures c[0] == a[0] + 1
{
  //:::  array_append.dfy(12,3)-(12,27): assignment (or return)
  // In Boogie
  //   assume true;
  // assert {:id "id8"} a#0 != null;
  // assume true;
  // assert {:id "id9"} 0 <= _System.array.Length(a#0) + 1;
  // havoc $nw;
  // assume $nw != null && $Is($nw, Tclass._System.array?(TInt));
  // assume !$Unbox(read($Heap, $nw, alloc)): bool;
  // assume _System.array.Length($nw) == _System.array.Length(a#0) + 1;
  // $Heap := update($Heap, $nw, alloc, $Box(true));
  // assume $IsGoodHeap($Heap);
  // assume $IsHeapAnchor($Heap);
  // c#0 := $nw;  (this assigment is not being tranlated as an assume)
  //              (and it is not captured, same problem I figured it out but more internal)
  //              (Unfortunatlye it seems that this has to be handle really on boogie no id call to save us
  // defass#c#0 := true;
  // assume {:captureState "array_append.dfy(10,26)"} true;
  c := new int[a.Length]; 
  c[0] := a[0] + 1;
}


//::: Name - Allocation never covered
//::: Description - Allocation generates an havoc assigment in Boogie (that makes it never be covered) (this was fixed on boogie by our PR)
//::: L24 - CovComplete