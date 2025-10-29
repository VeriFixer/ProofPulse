method append(a:array<int>, b:int) returns (c:array<int>)
  ensures  a.Length == c.Length
{
  //:::  array_append.dfy(12,3)-(12,27): assignment (or return)
  // Cannot understand why this is failing will need to debug

  // I serriously believe that the problem is this:
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

  // Not 100% debug the SMT is too much difficult as it is but highly certain
  //::: Need a way from boogie to generate SMT (to have the freedom to modify boogie itself)

  c := new int[a.Length]; //:: Need to figured it out this _allocation.dfy(29,3)-(29,25): assignment (or return)

}

//:: Need to try somethings to be 100% sure, if thats the case this has to be corrected
//:: In boogie->SMT translation itself and the problem is simmilar to the simple assigment
//:: But without a work around