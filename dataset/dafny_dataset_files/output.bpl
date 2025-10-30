
const $$Language$Dafny: bool
uses {
axiom $$Language$Dafny;
}

type Ty;

type Bv0 = int;

const unique TBool: Ty
uses {
axiom Tag(TBool) == TagBool;
}

const unique TChar: Ty
uses {
axiom Tag(TChar) == TagChar;
}

const unique TInt: Ty
uses {
axiom Tag(TInt) == TagInt;
}

const unique TField: Ty
uses {
axiom Tag(TField) == TagField;
}

const unique TReal: Ty
uses {
axiom Tag(TReal) == TagReal;
}

const unique TORDINAL: Ty
uses {
axiom Tag(TORDINAL) == TagORDINAL;
}

revealed function TBitvector(int) : Ty;

axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);

revealed function TSet(Ty) : Ty;

axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);

axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

revealed function TISet(Ty) : Ty;

axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);

axiom (forall t: Ty :: { TISet(t) } Tag(TISet(t)) == TagISet);

revealed function TMultiSet(Ty) : Ty;

axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);

axiom (forall t: Ty :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);

revealed function TSeq(Ty) : Ty;

axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);

axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

revealed function TMap(Ty, Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv0_TMap(TMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv1_TMap(TMap(t, u)) == u);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Tag(TMap(t, u)) == TagMap);

revealed function TIMap(Ty, Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv0_TIMap(TIMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv1_TIMap(TIMap(t, u)) == u);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Tag(TIMap(t, u)) == TagIMap);

revealed function Inv0_TBitvector(Ty) : int;

revealed function Inv0_TSet(Ty) : Ty;

revealed function Inv0_TISet(Ty) : Ty;

revealed function Inv0_TSeq(Ty) : Ty;

revealed function Inv0_TMultiSet(Ty) : Ty;

revealed function Inv0_TMap(Ty) : Ty;

revealed function Inv1_TMap(Ty) : Ty;

revealed function Inv0_TIMap(Ty) : Ty;

revealed function Inv1_TIMap(Ty) : Ty;

type TyTag;

revealed function Tag(Ty) : TyTag;

const unique TagBool: TyTag;

const unique TagChar: TyTag;

const unique TagInt: TyTag;

const unique TagField: TyTag;

const unique TagReal: TyTag;

const unique TagORDINAL: TyTag;

const unique TagSet: TyTag;

const unique TagISet: TyTag;

const unique TagMultiSet: TyTag;

const unique TagSeq: TyTag;

const unique TagMap: TyTag;

const unique TagIMap: TyTag;

const unique TagClass: TyTag;

type TyTagFamily;

revealed function TagFamily(Ty) : TyTagFamily;

revealed function {:identity} Lit<T>(x: T) : T
uses {
axiom (forall<T> x: T :: {:identity} { Lit(x): T } Lit(x): T == x);
}

axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)));

revealed function {:identity} LitInt(x: int) : int
uses {
axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);
}

axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)));

revealed function {:identity} LitReal(x: real) : real
uses {
axiom (forall x: real :: {:identity} { LitReal(x): real } LitReal(x): real == x);
}

axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)));

revealed function {:inline} char#IsChar(n: int) : bool
{
  (0 <= n && n < 55296) || (57344 <= n && n < 1114112)
}

type char;

revealed function char#FromInt(int) : char;

axiom (forall n: int :: 
  { char#FromInt(n) } 
  char#IsChar(n) ==> char#ToInt(char#FromInt(n)) == n);

revealed function char#ToInt(char) : int;

axiom (forall ch: char :: 
  { char#ToInt(ch) } 
  char#FromInt(char#ToInt(ch)) == ch && char#IsChar(char#ToInt(ch)));

revealed function char#Plus(char, char) : char;

axiom (forall a: char, b: char :: 
  { char#Plus(a, b) } 
  char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));

revealed function char#Minus(char, char) : char;

axiom (forall a: char, b: char :: 
  { char#Minus(a, b) } 
  char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

type ref;

const null: ref;

const locals: ref;

type FieldFamily;

const unique object_field: FieldFamily;

revealed function field_depth(f: Field) : int;

revealed function field_family(f: Field) : FieldFamily;

revealed function local_field(ff: FieldFamily, depth: int) : Field
uses {
axiom (forall ff: FieldFamily, depth: int :: 
  {:trigger local_field(ff, depth)} 
  field_depth(local_field(ff, depth)) == depth
     && field_family(local_field(ff, depth)) == ff);
}

type Box;

const $ArbitraryBoxValue: Box;

revealed function $Box<T>(T) : Box;

revealed function $Unbox<T>(Box) : T;

axiom (forall<T> x: T :: {:weight 3} { $Box(x) } $Unbox($Box(x)) == x);

axiom (forall<T> x: Box :: { $Unbox(x): T } $Box($Unbox(x): T) == x);

revealed function $IsBox(Box, Ty) : bool;

revealed function $IsAllocBox(Box, Ty, Heap) : bool;

axiom (forall bx: Box :: 
  { $IsBox(bx, TInt) } 
  $IsBox(bx, TInt) ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, TInt));

axiom (forall bx: Box :: 
  { $IsBox(bx, TReal) } 
  $IsBox(bx, TReal)
     ==> $Box($Unbox(bx): real) == bx && $Is($Unbox(bx): real, TReal));

axiom (forall bx: Box :: 
  { $IsBox(bx, TBool) } 
  $IsBox(bx, TBool)
     ==> $Box($Unbox(bx): bool) == bx && $Is($Unbox(bx): bool, TBool));

axiom (forall bx: Box :: 
  { $IsBox(bx, TChar) } 
  $IsBox(bx, TChar)
     ==> $Box($Unbox(bx): char) == bx && $Is($Unbox(bx): char, TChar));

axiom (forall bx: Box :: 
  { $IsBox(bx, TBitvector(0)) } 
  $IsBox(bx, TBitvector(0))
     ==> $Box($Unbox(bx): Bv0) == bx && $Is($Unbox(bx): Bv0, TBitvector(0)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSet(t)) } 
  $IsBox(bx, TSet(t))
     ==> $Box($Unbox(bx): Set) == bx && $Is($Unbox(bx): Set, TSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TISet(t)) } 
  $IsBox(bx, TISet(t))
     ==> $Box($Unbox(bx): ISet) == bx && $Is($Unbox(bx): ISet, TISet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TMultiSet(t)) } 
  $IsBox(bx, TMultiSet(t))
     ==> $Box($Unbox(bx): MultiSet) == bx && $Is($Unbox(bx): MultiSet, TMultiSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSeq(t)) } 
  $IsBox(bx, TSeq(t))
     ==> $Box($Unbox(bx): Seq) == bx && $Is($Unbox(bx): Seq, TSeq(t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TMap(s, t)) } 
  $IsBox(bx, TMap(s, t))
     ==> $Box($Unbox(bx): Map) == bx && $Is($Unbox(bx): Map, TMap(s, t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TIMap(s, t)) } 
  $IsBox(bx, TIMap(s, t))
     ==> $Box($Unbox(bx): IMap) == bx && $Is($Unbox(bx): IMap, TIMap(s, t)));

axiom (forall<T> v: T, t: Ty :: 
  { $IsBox($Box(v), t) } 
  $IsBox($Box(v), t) <==> $Is(v, t));

axiom (forall<T> v: T, t: Ty, h: Heap :: 
  { $IsAllocBox($Box(v), t, h) } 
  $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v, t, h));

revealed function $Is<T>(T, Ty) : bool;

axiom (forall v: int :: { $Is(v, TInt) } $Is(v, TInt));

axiom (forall v: real :: { $Is(v, TReal) } $Is(v, TReal));

axiom (forall v: bool :: { $Is(v, TBool) } $Is(v, TBool));

axiom (forall v: char :: { $Is(v, TChar) } $Is(v, TChar));

axiom (forall v: Field :: { $Is(v, TField) } $Is(v, TField));

axiom (forall v: ORDINAL :: { $Is(v, TORDINAL) } $Is(v, TORDINAL));

axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

axiom (forall v: Set, t0: Ty :: 
  { $Is(v, TSet(t0)) } 
  $Is(v, TSet(t0))
     <==> (forall bx: Box :: 
      { Set#IsMember(v, bx) } 
      Set#IsMember(v, bx) ==> $IsBox(bx, t0)));

axiom (forall v: ISet, t0: Ty :: 
  { $Is(v, TISet(t0)) } 
  $Is(v, TISet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0))
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(v, bx) } 
      0 < MultiSet#Multiplicity(v, bx) ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));

axiom (forall v: Seq, t0: Ty :: 
  { $Is(v, TSeq(t0)) } 
  $Is(v, TSeq(t0))
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Map, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Set#IsMember(Map#Domain(v), bx) } 
      Set#IsMember(Map#Domain(v), bx)
         ==> $IsBox(Map#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: Map, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     ==> $Is(Map#Domain(v), TSet(t0))
       && $Is(Map#Values(v), TSet(t1))
       && $Is(Map#Items(v), TSet(Tclass._System.Tuple2(t0, t1))));

axiom (forall v: IMap, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx] ==> $IsBox(IMap#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: IMap, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     ==> $Is(IMap#Domain(v), TISet(t0))
       && $Is(IMap#Values(v), TISet(t1))
       && $Is(IMap#Items(v), TISet(Tclass._System.Tuple2(t0, t1))));

revealed function $IsAlloc<T>(T, Ty, Heap) : bool;

axiom (forall h: Heap, v: int :: { $IsAlloc(v, TInt, h) } $IsAlloc(v, TInt, h));

axiom (forall h: Heap, v: real :: { $IsAlloc(v, TReal, h) } $IsAlloc(v, TReal, h));

axiom (forall h: Heap, v: bool :: { $IsAlloc(v, TBool, h) } $IsAlloc(v, TBool, h));

axiom (forall h: Heap, v: char :: { $IsAlloc(v, TChar, h) } $IsAlloc(v, TChar, h));

axiom (forall h: Heap, v: ORDINAL :: 
  { $IsAlloc(v, TORDINAL, h) } 
  $IsAlloc(v, TORDINAL, h));

axiom (forall v: Bv0, h: Heap :: 
  { $IsAlloc(v, TBitvector(0), h) } 
  $IsAlloc(v, TBitvector(0), h));

axiom (forall v: Set, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSet(t0), h) } 
  $IsAlloc(v, TSet(t0), h)
     <==> (forall bx: Box :: 
      { Set#IsMember(v, bx) } 
      Set#IsMember(v, bx) ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: ISet, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TISet(t0), h) } 
  $IsAlloc(v, TISet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: MultiSet, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TMultiSet(t0), h) } 
  $IsAlloc(v, TMultiSet(t0), h)
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(v, bx) } 
      0 < MultiSet#Multiplicity(v, bx) ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: Seq, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSeq(t0), h) } 
  $IsAlloc(v, TSeq(t0), h)
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsAllocBox(Seq#Index(v, i), t0, h)));

axiom (forall v: Map, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TMap(t0, t1), h) } 
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Set#IsMember(Map#Domain(v), bx) } 
      Set#IsMember(Map#Domain(v), bx)
         ==> $IsAllocBox(Map#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

axiom (forall v: IMap, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TIMap(t0, t1), h) } 
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx]
         ==> $IsAllocBox(IMap#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

revealed function $AlwaysAllocated(Ty) : bool;

axiom (forall ty: Ty :: 
  { $AlwaysAllocated(ty) } 
  $AlwaysAllocated(ty)
     ==> (forall h: Heap, v: Box :: 
      { $IsAllocBox(v, ty, h) } 
      $IsBox(v, ty) ==> $IsAllocBox(v, ty, h)));

revealed function $OlderTag(Heap) : bool;

type ClassName;

const unique class._System.int: ClassName;

const unique class._System.bool: ClassName;

const unique class._System.set: ClassName;

const unique class._System.seq: ClassName;

const unique class._System.multiset: ClassName;

revealed function Tclass._System.object?() : Ty
uses {
// Tclass._System.object? Tag
axiom Tag(Tclass._System.object?()) == Tagclass._System.object?
   && TagFamily(Tclass._System.object?()) == tytagFamily$object;
}

revealed function Tclass._System.Tuple2(Ty, Ty) : Ty;

revealed function dtype(ref) : Ty;

revealed function TypeTuple(a: ClassName, b: ClassName) : ClassName;

revealed function TypeTupleCar(ClassName) : ClassName;

revealed function TypeTupleCdr(ClassName) : ClassName;

axiom (forall a: ClassName, b: ClassName :: 
  { TypeTuple(a, b) } 
  TypeTupleCar(TypeTuple(a, b)) == a && TypeTupleCdr(TypeTuple(a, b)) == b);

type HandleType;

revealed function SetRef_to_SetBox(s: [ref]bool) : Set;

axiom (forall s: [ref]bool, bx: Box :: 
  { Set#IsMember(SetRef_to_SetBox(s), bx) } 
  Set#IsMember(SetRef_to_SetBox(s), bx) == s[$Unbox(bx): ref]);

axiom (forall s: [ref]bool :: 
  { SetRef_to_SetBox(s) } 
  $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object?())));

revealed function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;

type DatatypeType;

type DtCtorId;

revealed function DatatypeCtorId(DatatypeType) : DtCtorId;

revealed function DtRank(DatatypeType) : int;

revealed function BoxRank(Box) : int;

axiom (forall d: DatatypeType :: { BoxRank($Box(d)) } BoxRank($Box(d)) == DtRank(d));

type ORDINAL = Box;

revealed function ORD#IsNat(ORDINAL) : bool;

revealed function ORD#Offset(ORDINAL) : int;

axiom (forall o: ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));

revealed function {:inline} ORD#IsLimit(o: ORDINAL) : bool
{
  ORD#Offset(o) == 0
}

revealed function {:inline} ORD#IsSucc(o: ORDINAL) : bool
{
  0 < ORD#Offset(o)
}

revealed function ORD#FromNat(int) : ORDINAL;

axiom (forall n: int :: 
  { ORD#FromNat(n) } 
  0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);

axiom (forall o: ORDINAL :: 
  { ORD#Offset(o) } { ORD#IsNat(o) } 
  ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));

revealed function ORD#Less(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Less(o, p) } 
  (ORD#Less(o, p) ==> o != p)
     && (ORD#IsNat(o) && !ORD#IsNat(p) ==> ORD#Less(o, p))
     && (ORD#IsNat(o) && ORD#IsNat(p)
       ==> ORD#Less(o, p) == (ORD#Offset(o) < ORD#Offset(p)))
     && (ORD#Less(o, p) && ORD#IsNat(p) ==> ORD#IsNat(o)));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Less(o, p), ORD#Less(p, o) } 
  ORD#Less(o, p) || o == p || ORD#Less(p, o));

axiom (forall o: ORDINAL, p: ORDINAL, r: ORDINAL :: 
  { ORD#Less(o, p), ORD#Less(p, r) } { ORD#Less(o, p), ORD#Less(o, r) } 
  ORD#Less(o, p) && ORD#Less(p, r) ==> ORD#Less(o, r));

revealed function ORD#LessThanLimit(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#LessThanLimit(o, p) } 
  ORD#LessThanLimit(o, p) == ORD#Less(o, p));

revealed function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (ORD#IsNat(ORD#Plus(o, p)) ==> ORD#IsNat(o) && ORD#IsNat(p))
     && (ORD#IsNat(p)
       ==> ORD#IsNat(ORD#Plus(o, p)) == ORD#IsNat(o)
         && ORD#Offset(ORD#Plus(o, p)) == ORD#Offset(o) + ORD#Offset(p)));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (o == ORD#Plus(o, p) || ORD#Less(o, ORD#Plus(o, p)))
     && (p == ORD#Plus(o, p) || ORD#Less(p, ORD#Plus(o, p))));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Plus(o, p) } 
  (o == ORD#FromNat(0) ==> ORD#Plus(o, p) == p)
     && (p == ORD#FromNat(0) ==> ORD#Plus(o, p) == o));

revealed function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Minus(o, p) } 
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> ORD#IsNat(ORD#Minus(o, p)) == ORD#IsNat(o)
       && ORD#Offset(ORD#Minus(o, p)) == ORD#Offset(o) - ORD#Offset(p));

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#Minus(o, p) } 
  ORD#IsNat(p) && ORD#Offset(p) <= ORD#Offset(o)
     ==> (p == ORD#FromNat(0) && ORD#Minus(o, p) == o)
       || (p != ORD#FromNat(0) && ORD#Less(ORD#Minus(o, p), o)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n
     ==> ORD#Plus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Plus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && m + n <= ORD#Offset(o)
     ==> ORD#Minus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
       == ORD#Minus(o, ORD#FromNat(m + n)));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Minus(ORD#Plus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(n - m))));

axiom (forall o: ORDINAL, m: int, n: int :: 
  { ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n)) } 
  0 <= m && 0 <= n && n <= ORD#Offset(o) + m
     ==> (0 <= m - n
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Minus(o, ORD#FromNat(m - n)))
       && (m - n <= 0
         ==> ORD#Plus(ORD#Minus(o, ORD#FromNat(m)), ORD#FromNat(n))
           == ORD#Plus(o, ORD#FromNat(n - m))));

type LayerType;

const $LZ: LayerType;

revealed function $LS(LayerType) : LayerType;

revealed function AsFuelBottom(LayerType) : LayerType;

revealed function AtLayer<A>([LayerType]A, LayerType) : A;

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, ly) } 
  AtLayer(f, ly) == f[ly]);

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, $LS(ly)) } 
  AtLayer(f, $LS(ly)) == AtLayer(f, ly));

type Field;

revealed function FDim(Field) : int
uses {
axiom FDim(alloc) == 0;
}

revealed function IndexField(int) : Field;

axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);

revealed function IndexField_Inverse(Field) : int;

axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

revealed function MultiIndexField(Field, int) : Field;

axiom (forall f: Field, i: int :: 
  { MultiIndexField(f, i) } 
  FDim(MultiIndexField(f, i)) == FDim(f) + 1);

revealed function MultiIndexField_Inverse0(Field) : Field;

revealed function MultiIndexField_Inverse1(Field) : int;

axiom (forall f: Field, i: int :: 
  { MultiIndexField(f, i) } 
  MultiIndexField_Inverse0(MultiIndexField(f, i)) == f
     && MultiIndexField_Inverse1(MultiIndexField(f, i)) == i);

revealed function DeclType(Field) : ClassName;

type NameFamily;

revealed function DeclName(Field) : NameFamily
uses {
axiom DeclName(alloc) == allocName;
}

revealed function FieldOfDecl(ClassName, NameFamily) : Field;

axiom (forall cl: ClassName, nm: NameFamily :: 
  { FieldOfDecl(cl, nm): Field } 
  DeclType(FieldOfDecl(cl, nm): Field) == cl
     && DeclName(FieldOfDecl(cl, nm): Field) == nm);

revealed function $IsGhostField(Field) : bool
uses {
axiom $IsGhostField(alloc);
}

axiom (forall h: Heap, k: Heap :: 
  { $HeapSuccGhost(h, k) } 
  $HeapSuccGhost(h, k)
     ==> $HeapSucc(h, k)
       && (forall o: ref, f: Field :: 
        { read(k, o, f) } 
        !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

axiom (forall<T> h: Heap, k: Heap, v: T, t: Ty :: 
  { $HeapSucc(h, k), $IsAlloc(v, t, h) } 
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));

axiom (forall h: Heap, k: Heap, bx: Box, t: Ty :: 
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) } 
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

const unique alloc: Field;

const unique allocName: NameFamily;

revealed function _System.array.Length(a: ref) : int;

axiom (forall o: ref :: { _System.array.Length(o) } 0 <= _System.array.Length(o));

revealed function Int(x: real) : int
uses {
axiom (forall x: real :: { Int(x): int } Int(x): int == int(x));
}

revealed function Real(x: int) : real
uses {
axiom (forall x: int :: { Real(x): real } Real(x): real == real(x));
}

axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);

revealed function {:inline} _System.real.Floor(x: real) : int
{
  Int(x)
}

type Heap = [ref][Field]Box;

revealed function {:inline} read(H: Heap, r: ref, f: Field) : Box
{
  H[r][f]
}

revealed function {:inline} update(H: Heap, r: ref, f: Field, v: Box) : Heap
{
  H[r := H[r][f := v]]
}

revealed function $IsGoodHeap(Heap) : bool;

revealed function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

const $OneHeap: Heap
uses {
axiom $IsGoodHeap($OneHeap);
}

revealed function $HeapSucc(Heap, Heap) : bool;

axiom (forall h: Heap, r: ref, f: Field, x: Box :: 
  { update(h, r, f, x) } 
  $IsGoodHeap(update(h, r, f, x)) ==> $HeapSucc(h, update(h, r, f, x)));

axiom (forall a: Heap, b: Heap, c: Heap :: 
  { $HeapSucc(a, b), $HeapSucc(b, c) } 
  a != c ==> $HeapSucc(a, b) && $HeapSucc(b, c) ==> $HeapSucc(a, c));

axiom (forall h: Heap, k: Heap :: 
  { $HeapSucc(h, k) } 
  $HeapSucc(h, k)
     ==> (forall o: ref :: 
      { read(k, o, alloc) } 
      $Unbox(read(h, o, alloc)) ==> $Unbox(read(k, o, alloc))));

revealed function $HeapSuccGhost(Heap, Heap) : bool;

procedure $YieldHavoc(this: ref, rds: Set, nw: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> 
      $o == this || Set#IsMember(rds, $Box($o)) || Set#IsMember(nw, $Box($o))
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc0(this: ref, rds: Set, modi: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> 
      Set#IsMember(rds, $Box($o)) && !Set#IsMember(modi, $Box($o)) && $o != this
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc1(this: ref, modi: Set, nw: Set);
  modifies $Heap;
  ensures (forall $o: ref, $f: Field :: 
    { read($Heap, $o, $f) } 
    $o != null && $Unbox(read(old($Heap), $o, alloc))
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || $o == this
         || Set#IsMember(modi, $Box($o))
         || Set#IsMember(nw, $Box($o)));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field) returns (s: Set);
  ensures (forall bx: Box :: 
    { Set#IsMember(s, bx) } 
    Set#IsMember(s, bx)
       <==> Set#IsMember($Unbox(read(newHeap, this, NW)): Set, bx)
         || (
          $Unbox(bx) != null
           && !$Unbox(read(prevHeap, $Unbox(bx): ref, alloc))
           && $Unbox(read(newHeap, $Unbox(bx): ref, alloc))));



type Set;

revealed function Set#Card(s: Set) : int;

axiom (forall s: Set :: { Set#Card(s) } 0 <= Set#Card(s));

revealed function Set#Empty() : Set;

revealed function Set#IsMember(s: Set, o: Box) : bool;

axiom (forall o: Box :: 
  { Set#IsMember(Set#Empty(), o) } 
  !Set#IsMember(Set#Empty(), o));

axiom (forall s: Set :: 
  { Set#Card(s) } 
  (Set#Card(s) == 0 <==> s == Set#Empty())
     && (Set#Card(s) != 0
       ==> (exists x: Box :: { Set#IsMember(s, x) } Set#IsMember(s, x))));

revealed function Set#UnionOne(s: Set, o: Box) : Set;

axiom (forall a: Set, x: Box, o: Box :: 
  { Set#IsMember(Set#UnionOne(a, x), o) } 
  Set#IsMember(Set#UnionOne(a, x), o) <==> o == x || Set#IsMember(a, o));

axiom (forall a: Set, x: Box :: 
  { Set#UnionOne(a, x) } 
  Set#IsMember(Set#UnionOne(a, x), x));

axiom (forall a: Set, x: Box, y: Box :: 
  { Set#UnionOne(a, x), Set#IsMember(a, y) } 
  Set#IsMember(a, y) ==> Set#IsMember(Set#UnionOne(a, x), y));

axiom (forall a: Set, x: Box :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  Set#IsMember(a, x) ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

axiom (forall a: Set, x: Box :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  !Set#IsMember(a, x) ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

revealed function Set#Union(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Union(a, b), o) } 
  Set#IsMember(Set#Union(a, b), o) <==> Set#IsMember(a, o) || Set#IsMember(b, o));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Union(a, b), Set#IsMember(a, y) } 
  Set#IsMember(a, y) ==> Set#IsMember(Set#Union(a, b), y));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Union(a, b), Set#IsMember(b, y) } 
  Set#IsMember(b, y) ==> Set#IsMember(Set#Union(a, b), y));

axiom (forall a: Set, b: Set :: 
  { Set#Union(a, b) } 
  Set#Disjoint(a, b)
     ==> Set#Difference(Set#Union(a, b), a) == b
       && Set#Difference(Set#Union(a, b), b) == a);

revealed function Set#Intersection(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Intersection(a, b), o) } 
  Set#IsMember(Set#Intersection(a, b), o)
     <==> Set#IsMember(a, o) && Set#IsMember(b, o));

axiom (forall a: Set, b: Set :: 
  { Set#Union(Set#Union(a, b), b) } 
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Union(a, Set#Union(a, b)) } 
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Intersection(Set#Intersection(a, b), b) } 
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Intersection(a, Set#Intersection(a, b)) } 
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

axiom (forall a: Set, b: Set :: 
  { Set#Card(Set#Union(a, b)) } { Set#Card(Set#Intersection(a, b)) } 
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
     == Set#Card(a) + Set#Card(b));

revealed function Set#Difference(a: Set, b: Set) : Set;

axiom (forall a: Set, b: Set, o: Box :: 
  { Set#IsMember(Set#Difference(a, b), o) } 
  Set#IsMember(Set#Difference(a, b), o)
     <==> Set#IsMember(a, o) && !Set#IsMember(b, o));

axiom (forall a: Set, b: Set, y: Box :: 
  { Set#Difference(a, b), Set#IsMember(b, y) } 
  Set#IsMember(b, y) ==> !Set#IsMember(Set#Difference(a, b), y));

axiom (forall a: Set, b: Set :: 
  { Set#Card(Set#Difference(a, b)) } 
  Set#Card(Set#Difference(a, b))
         + Set#Card(Set#Difference(b, a))
         + Set#Card(Set#Intersection(a, b))
       == Set#Card(Set#Union(a, b))
     && Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

revealed function Set#Subset(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Subset(a, b) } 
  Set#Subset(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      Set#IsMember(a, o) ==> Set#IsMember(b, o)));

revealed function Set#Equal(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Equal(a, b) } 
  Set#Equal(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      Set#IsMember(a, o) <==> Set#IsMember(b, o)));

axiom (forall a: Set, b: Set :: { Set#Equal(a, b) } Set#Equal(a, b) ==> a == b);

revealed function Set#Disjoint(a: Set, b: Set) : bool;

axiom (forall a: Set, b: Set :: 
  { Set#Disjoint(a, b) } 
  Set#Disjoint(a, b)
     <==> (forall o: Box :: 
      { Set#IsMember(a, o) } { Set#IsMember(b, o) } 
      !Set#IsMember(a, o) || !Set#IsMember(b, o)));

revealed function Set#FromBoogieMap([Box]bool) : Set;

axiom (forall m: [Box]bool, bx: Box :: 
  { Set#IsMember(Set#FromBoogieMap(m), bx) } 
  Set#IsMember(Set#FromBoogieMap(m), bx) == m[bx]);

type ISet = [Box]bool;

revealed function ISet#Empty() : ISet;

axiom (forall o: Box :: { ISet#Empty()[o] } !ISet#Empty()[o]);

revealed function ISet#FromSet(Set) : ISet;

axiom (forall s: Set, bx: Box :: 
  { ISet#FromSet(s)[bx] } 
  ISet#FromSet(s)[bx] == Set#IsMember(s, bx));

revealed function ISet#UnionOne(ISet, Box) : ISet;

axiom (forall a: ISet, x: Box, o: Box :: 
  { ISet#UnionOne(a, x)[o] } 
  ISet#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall a: ISet, x: Box :: { ISet#UnionOne(a, x) } ISet#UnionOne(a, x)[x]);

axiom (forall a: ISet, x: Box, y: Box :: 
  { ISet#UnionOne(a, x), a[y] } 
  a[y] ==> ISet#UnionOne(a, x)[y]);

revealed function ISet#Union(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Union(a, b)[o] } 
  ISet#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Union(a, b), a[y] } 
  a[y] ==> ISet#Union(a, b)[y]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Union(a, b), b[y] } 
  b[y] ==> ISet#Union(a, b)[y]);

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(a, b) } 
  ISet#Disjoint(a, b)
     ==> ISet#Difference(ISet#Union(a, b), a) == b
       && ISet#Difference(ISet#Union(a, b), b) == a);

revealed function ISet#Intersection(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Intersection(a, b)[o] } 
  ISet#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(ISet#Union(a, b), b) } 
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Union(a, ISet#Union(a, b)) } 
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Intersection(ISet#Intersection(a, b), b) } 
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));

axiom (forall a: ISet, b: ISet :: 
  { ISet#Intersection(a, ISet#Intersection(a, b)) } 
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));

revealed function ISet#Difference(ISet, ISet) : ISet;

axiom (forall a: ISet, b: ISet, o: Box :: 
  { ISet#Difference(a, b)[o] } 
  ISet#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall a: ISet, b: ISet, y: Box :: 
  { ISet#Difference(a, b), b[y] } 
  b[y] ==> !ISet#Difference(a, b)[y]);

revealed function ISet#Subset(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Subset(a, b) } 
  ISet#Subset(a, b) <==> (forall o: Box :: { a[o] } { b[o] } a[o] ==> b[o]));

revealed function ISet#Equal(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Equal(a, b) } 
  ISet#Equal(a, b) <==> (forall o: Box :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall a: ISet, b: ISet :: { ISet#Equal(a, b) } ISet#Equal(a, b) ==> a == b);

revealed function ISet#Disjoint(ISet, ISet) : bool;

axiom (forall a: ISet, b: ISet :: 
  { ISet#Disjoint(a, b) } 
  ISet#Disjoint(a, b) <==> (forall o: Box :: { a[o] } { b[o] } !a[o] || !b[o]));

revealed function Math#min(a: int, b: int) : int;

axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);

axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);

axiom (forall a: int, b: int :: 
  { Math#min(a, b) } 
  Math#min(a, b) == a || Math#min(a, b) == b);

revealed function Math#clip(a: int) : int;

axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);

axiom (forall a: int :: { Math#clip(a) } a < 0 ==> Math#clip(a) == 0);

type MultiSet;

revealed function MultiSet#Multiplicity(m: MultiSet, o: Box) : int;

revealed function MultiSet#UpdateMultiplicity(m: MultiSet, o: Box, n: int) : MultiSet;

axiom (forall m: MultiSet, o: Box, n: int, p: Box :: 
  { MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p) } 
  0 <= n
     ==> (o == p ==> MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p) == n)
       && (o != p
         ==> MultiSet#Multiplicity(MultiSet#UpdateMultiplicity(m, o, n), p)
           == MultiSet#Multiplicity(m, p)));

revealed function $IsGoodMultiSet(ms: MultiSet) : bool;

axiom (forall ms: MultiSet :: 
  { $IsGoodMultiSet(ms) } 
  $IsGoodMultiSet(ms)
     <==> (forall bx: Box :: 
      { MultiSet#Multiplicity(ms, bx) } 
      0 <= MultiSet#Multiplicity(ms, bx)
         && MultiSet#Multiplicity(ms, bx) <= MultiSet#Card(ms)));

revealed function MultiSet#Card(m: MultiSet) : int;

axiom (forall s: MultiSet :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));

axiom (forall s: MultiSet, x: Box, n: int :: 
  { MultiSet#Card(MultiSet#UpdateMultiplicity(s, x, n)) } 
  0 <= n
     ==> MultiSet#Card(MultiSet#UpdateMultiplicity(s, x, n))
       == MultiSet#Card(s) - MultiSet#Multiplicity(s, x) + n);

revealed function MultiSet#Empty() : MultiSet;

axiom (forall o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Empty(), o) } 
  MultiSet#Multiplicity(MultiSet#Empty(), o) == 0);

axiom (forall s: MultiSet :: 
  { MultiSet#Card(s) } 
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty())
     && (MultiSet#Card(s) != 0
       ==> (exists x: Box :: 
        { MultiSet#Multiplicity(s, x) } 
        0 < MultiSet#Multiplicity(s, x))));

revealed function MultiSet#Singleton(o: Box) : MultiSet;

axiom (forall r: Box, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Singleton(r), o) } 
  (MultiSet#Multiplicity(MultiSet#Singleton(r), o) == 1 <==> r == o)
     && (MultiSet#Multiplicity(MultiSet#Singleton(r), o) == 0 <==> r != o));

axiom (forall r: Box :: 
  { MultiSet#Singleton(r) } 
  MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

revealed function MultiSet#UnionOne(m: MultiSet, o: Box) : MultiSet;

axiom (forall a: MultiSet, x: Box, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#UnionOne(a, x), o) } 
  0 < MultiSet#Multiplicity(MultiSet#UnionOne(a, x), o)
     <==> o == x || 0 < MultiSet#Multiplicity(a, o));

axiom (forall a: MultiSet, x: Box :: 
  { MultiSet#UnionOne(a, x) } 
  MultiSet#Multiplicity(MultiSet#UnionOne(a, x), x)
     == MultiSet#Multiplicity(a, x) + 1);

axiom (forall a: MultiSet, x: Box, y: Box :: 
  { MultiSet#UnionOne(a, x), MultiSet#Multiplicity(a, y) } 
  0 < MultiSet#Multiplicity(a, y)
     ==> 0 < MultiSet#Multiplicity(MultiSet#UnionOne(a, x), y));

axiom (forall a: MultiSet, x: Box, y: Box :: 
  { MultiSet#UnionOne(a, x), MultiSet#Multiplicity(a, y) } 
  x != y
     ==> MultiSet#Multiplicity(a, y) == MultiSet#Multiplicity(MultiSet#UnionOne(a, x), y));

axiom (forall a: MultiSet, x: Box :: 
  { MultiSet#Card(MultiSet#UnionOne(a, x)) } 
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);

revealed function MultiSet#Union(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Union(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Union(a, b), o)
     == MultiSet#Multiplicity(a, o) + MultiSet#Multiplicity(b, o));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Card(MultiSet#Union(a, b)) } 
  MultiSet#Card(MultiSet#Union(a, b)) == MultiSet#Card(a) + MultiSet#Card(b));

revealed function MultiSet#Intersection(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Intersection(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Intersection(a, b), o)
     == Math#min(MultiSet#Multiplicity(a, o), MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Intersection(MultiSet#Intersection(a, b), b) } 
  MultiSet#Intersection(MultiSet#Intersection(a, b), b)
     == MultiSet#Intersection(a, b));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) } 
  MultiSet#Intersection(a, MultiSet#Intersection(a, b))
     == MultiSet#Intersection(a, b));

revealed function MultiSet#Difference(a: MultiSet, b: MultiSet) : MultiSet;

axiom (forall a: MultiSet, b: MultiSet, o: Box :: 
  { MultiSet#Multiplicity(MultiSet#Difference(a, b), o) } 
  MultiSet#Multiplicity(MultiSet#Difference(a, b), o)
     == Math#clip(MultiSet#Multiplicity(a, o) - MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet, y: Box :: 
  { MultiSet#Difference(a, b), MultiSet#Multiplicity(b, y), MultiSet#Multiplicity(a, y) } 
  MultiSet#Multiplicity(a, y) <= MultiSet#Multiplicity(b, y)
     ==> MultiSet#Multiplicity(MultiSet#Difference(a, b), y) == 0);

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Card(MultiSet#Difference(a, b)) } 
  MultiSet#Card(MultiSet#Difference(a, b))
         + MultiSet#Card(MultiSet#Difference(b, a))
         + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
       == MultiSet#Card(MultiSet#Union(a, b))
     && MultiSet#Card(MultiSet#Difference(a, b))
       == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

revealed function MultiSet#Subset(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Subset(a, b) } 
  MultiSet#Subset(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) <= MultiSet#Multiplicity(b, o)));

revealed function MultiSet#Equal(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) == MultiSet#Multiplicity(b, o)));

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b) ==> a == b);

revealed function MultiSet#Disjoint(a: MultiSet, b: MultiSet) : bool;

axiom (forall a: MultiSet, b: MultiSet :: 
  { MultiSet#Disjoint(a, b) } 
  MultiSet#Disjoint(a, b)
     <==> (forall o: Box :: 
      { MultiSet#Multiplicity(a, o) } { MultiSet#Multiplicity(b, o) } 
      MultiSet#Multiplicity(a, o) == 0 || MultiSet#Multiplicity(b, o) == 0));

revealed function MultiSet#FromSet(s: Set) : MultiSet;

axiom (forall s: Set, a: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSet(s), a) } 
  (MultiSet#Multiplicity(MultiSet#FromSet(s), a) == 0 <==> !Set#IsMember(s, a))
     && (MultiSet#Multiplicity(MultiSet#FromSet(s), a) == 1 <==> Set#IsMember(s, a)));

axiom (forall s: Set :: 
  { MultiSet#Card(MultiSet#FromSet(s)) } 
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

revealed function MultiSet#FromSeq(s: Seq) : MultiSet
uses {
axiom MultiSet#FromSeq(Seq#Empty()) == MultiSet#Empty();
}

axiom (forall s: Seq :: { MultiSet#FromSeq(s) } $IsGoodMultiSet(MultiSet#FromSeq(s)));

axiom (forall s: Seq :: 
  { MultiSet#Card(MultiSet#FromSeq(s)) } 
  MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));

axiom (forall s: Seq, v: Box :: 
  { MultiSet#FromSeq(Seq#Build(s, v)) } 
  MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v));

axiom (forall a: Seq, b: Seq :: 
  { MultiSet#FromSeq(Seq#Append(a, b)) } 
  MultiSet#FromSeq(Seq#Append(a, b))
     == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)));

axiom (forall s: Seq, i: int, v: Box, x: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSeq(Seq#Update(s, i, v)), x) } 
  0 <= i && i < Seq#Length(s)
     ==> MultiSet#Multiplicity(MultiSet#FromSeq(Seq#Update(s, i, v)), x)
       == MultiSet#Multiplicity(MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s, i))), 
          MultiSet#Singleton(v)), 
        x));

axiom (forall s: Seq, x: Box :: 
  { MultiSet#Multiplicity(MultiSet#FromSeq(s), x) } 
  (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && x == Seq#Index(s, i))
     <==> 0 < MultiSet#Multiplicity(MultiSet#FromSeq(s), x));

type Seq;

revealed function Seq#Length(s: Seq) : int;

axiom (forall s: Seq :: { Seq#Length(s) } 0 <= Seq#Length(s));

revealed function Seq#Empty() : Seq
uses {
axiom Seq#Length(Seq#Empty()) == 0;
}

axiom (forall s: Seq :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());

revealed function Seq#Build(s: Seq, val: Box) : Seq;

revealed function Seq#Build_inv0(s: Seq) : Seq;

revealed function Seq#Build_inv1(s: Seq) : Box;

axiom (forall s: Seq, val: Box :: 
  { Seq#Build(s, val) } 
  Seq#Build_inv0(Seq#Build(s, val)) == s
     && Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall s: Seq, v: Box :: 
  { Seq#Build(s, v) } 
  Seq#Length(Seq#Build(s, v)) == 1 + Seq#Length(s));

axiom (forall s: Seq, i: int, v: Box :: 
  { Seq#Index(Seq#Build(s, v), i) } 
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == v)
     && (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == Seq#Index(s, i)));

axiom (forall s0: Seq, s1: Seq :: 
  { Seq#Length(Seq#Append(s0, s1)) } 
  Seq#Length(Seq#Append(s0, s1)) == Seq#Length(s0) + Seq#Length(s1));

revealed function Seq#Index(s: Seq, i: int) : Box;

axiom (forall s0: Seq, s1: Seq, n: int :: 
  { Seq#Index(Seq#Append(s0, s1), n) } 
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s0, n))
     && (Seq#Length(s0) <= n
       ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

revealed function Seq#Update(s: Seq, i: int, val: Box) : Seq;

axiom (forall s: Seq, i: int, v: Box :: 
  { Seq#Length(Seq#Update(s, i, v)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s, i, v)) == Seq#Length(s));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Index(Seq#Update(s, i, v), n) } 
  0 <= n && n < Seq#Length(s)
     ==> (i == n ==> Seq#Index(Seq#Update(s, i, v), n) == v)
       && (i != n ==> Seq#Index(Seq#Update(s, i, v), n) == Seq#Index(s, n)));

revealed function Seq#Append(s0: Seq, s1: Seq) : Seq;

revealed function Seq#Contains(s: Seq, val: Box) : bool;

axiom (forall s: Seq, x: Box :: 
  { Seq#Contains(s, x) } 
  Seq#Contains(s, x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall x: Box :: 
  { Seq#Contains(Seq#Empty(), x) } 
  !Seq#Contains(Seq#Empty(), x));

axiom (forall s0: Seq, s1: Seq, x: Box :: 
  { Seq#Contains(Seq#Append(s0, s1), x) } 
  Seq#Contains(Seq#Append(s0, s1), x)
     <==> Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall s: Seq, v: Box, x: Box :: 
  { Seq#Contains(Seq#Build(s, v), x) } 
  Seq#Contains(Seq#Build(s, v), x) <==> v == x || Seq#Contains(s, x));

axiom (forall s: Seq, n: int, x: Box :: 
  { Seq#Contains(Seq#Take(s, n), x) } 
  Seq#Contains(Seq#Take(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall s: Seq, n: int, x: Box :: 
  { Seq#Contains(Seq#Drop(s, n), x) } 
  Seq#Contains(Seq#Drop(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

revealed function Seq#Equal(s0: Seq, s1: Seq) : bool;

axiom (forall s0: Seq, s1: Seq :: 
  { Seq#Equal(s0, s1) } 
  Seq#Equal(s0, s1)
     <==> Seq#Length(s0) == Seq#Length(s1)
       && (forall j: int :: 
        { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

axiom (forall a: Seq, b: Seq :: { Seq#Equal(a, b) } Seq#Equal(a, b) ==> a == b);

revealed function Seq#SameUntil(s0: Seq, s1: Seq, n: int) : bool;

axiom (forall s0: Seq, s1: Seq, n: int :: 
  { Seq#SameUntil(s0, s1, n) } 
  Seq#SameUntil(s0, s1, n)
     <==> (forall j: int :: 
      { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
      0 <= j && j < n ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

revealed function Seq#Take(s: Seq, howMany: int) : Seq;

axiom (forall s: Seq, n: int :: 
  { Seq#Length(Seq#Take(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s, n)) == n);

axiom (forall s: Seq, n: int, j: int :: 
  {:weight 11} { Seq#Index(Seq#Take(s, n), j) } { Seq#Index(s, j), Seq#Take(s, n) } 
  0 <= j && j < n && j < Seq#Length(s)
     ==> Seq#Index(Seq#Take(s, n), j) == Seq#Index(s, j));

revealed function Seq#Drop(s: Seq, howMany: int) : Seq;

axiom (forall s: Seq, n: int :: 
  { Seq#Length(Seq#Drop(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s, n)) == Seq#Length(s) - n);

axiom (forall s: Seq, n: int, j: int :: 
  {:weight 11} { Seq#Index(Seq#Drop(s, n), j) } 
  0 <= n && 0 <= j && j < Seq#Length(s) - n
     ==> Seq#Index(Seq#Drop(s, n), j) == Seq#Index(s, j + n));

axiom (forall s: Seq, n: int, k: int :: 
  {:weight 11} { Seq#Index(s, k), Seq#Drop(s, n) } 
  0 <= n && n <= k && k < Seq#Length(s)
     ==> Seq#Index(Seq#Drop(s, n), k - n) == Seq#Index(s, k));

axiom (forall s: Seq, t: Seq, n: int :: 
  { Seq#Take(Seq#Append(s, t), n) } { Seq#Drop(Seq#Append(s, t), n) } 
  n == Seq#Length(s)
     ==> Seq#Take(Seq#Append(s, t), n) == s && Seq#Drop(Seq#Append(s, t), n) == t);

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  n <= i && i < Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= n && n <= i && i < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i - n, v));

axiom (forall s: Seq, i: int, v: Box, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

axiom (forall s: Seq, v: Box, n: int :: 
  { Seq#Drop(Seq#Build(s, v), n) } 
  0 <= n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v));

axiom (forall s: Seq, n: int :: { Seq#Drop(s, n) } n == 0 ==> Seq#Drop(s, n) == s);

axiom (forall s: Seq, n: int :: 
  { Seq#Take(s, n) } 
  n == 0 ==> Seq#Take(s, n) == Seq#Empty());

axiom (forall s: Seq, m: int, n: int :: 
  { Seq#Drop(Seq#Drop(s, m), n) } 
  0 <= m && 0 <= n && m + n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m + n));

axiom (forall s: Seq, bx: Box, t: Ty :: 
  { $Is(Seq#Build(s, bx), TSeq(t)) } 
  $Is(s, TSeq(t)) && $IsBox(bx, t) ==> $Is(Seq#Build(s, bx), TSeq(t)));

revealed function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType) : Seq;

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType :: 
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq) } 
  $IsGoodHeap(heap) && 0 <= len
     ==> Seq#Length(Seq#Create(ty, heap, len, init): Seq) == len);

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int :: 
  { Seq#Index(Seq#Create(ty, heap, len, init), i) } 
  $IsGoodHeap(heap) && 0 <= i && i < len
     ==> Seq#Index(Seq#Create(ty, heap, len, init), i)
       == Apply1(TInt, ty, heap, init, $Box(i)));

revealed function Seq#FromArray(h: Heap, a: ref) : Seq;

axiom (forall h: Heap, a: ref :: 
  { Seq#Length(Seq#FromArray(h, a)) } 
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));

axiom (forall h: Heap, a: ref :: 
  { Seq#FromArray(h, a) } 
  (forall i: int :: 
    { read(h, a, IndexField(i)) } { Seq#Index(Seq#FromArray(h, a): Seq, i) } 
    0 <= i && i < Seq#Length(Seq#FromArray(h, a))
       ==> Seq#Index(Seq#FromArray(h, a), i) == read(h, a, IndexField(i))));

axiom (forall h0: Heap, h1: Heap, a: ref :: 
  { Seq#FromArray(h1, a), $HeapSucc(h0, h1) } 
  $IsGoodHeap(h0) && $IsGoodHeap(h1) && $HeapSucc(h0, h1) && h0[a] == h1[a]
     ==> Seq#FromArray(h0, a) == Seq#FromArray(h1, a));

axiom (forall h: Heap, i: int, v: Box, a: ref :: 
  { Seq#FromArray(update(h, a, IndexField(i), v), a) } 
  0 <= i && i < _System.array.Length(a)
     ==> Seq#FromArray(update(h, a, IndexField(i), v), a)
       == Seq#Update(Seq#FromArray(h, a), i, v));

axiom (forall h: Heap, a: ref, n0: int, n1: int :: 
  { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) } 
  n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a)
     ==> Seq#Take(Seq#FromArray(h, a), n1)
       == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field)));

revealed function Seq#Rank(Seq) : int;

axiom (forall s: Seq, i: int :: 
  { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) } 
  0 <= i && i < Seq#Length(s)
     ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s));

axiom (forall s: Seq, i: int :: 
  { Seq#Rank(Seq#Drop(s, i)) } 
  0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s));

axiom (forall s: Seq, i: int :: 
  { Seq#Rank(Seq#Take(s, i)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s));

axiom (forall s: Seq, i: int, j: int :: 
  { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) } 
  0 <= i && i < j && j <= Seq#Length(s)
     ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s));

type Map;

revealed function Map#Domain(Map) : Set;

revealed function Map#Elements(Map) : [Box]Box;

revealed function Map#Card(Map) : int;

axiom (forall m: Map :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall m: Map :: { Map#Card(m) } Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall m: Map :: 
  { Map#Domain(m) } 
  m == Map#Empty() || (exists k: Box :: Set#IsMember(Map#Domain(m), k)));

axiom (forall m: Map :: 
  { Map#Values(m) } 
  m == Map#Empty() || (exists v: Box :: Set#IsMember(Map#Values(m), v)));

axiom (forall m: Map :: 
  { Map#Items(m) } 
  m == Map#Empty()
     || (exists k: Box, v: Box :: 
      Set#IsMember(Map#Items(m), $Box(#_System._tuple#2._#Make2(k, v)))));

axiom (forall m: Map :: 
  { Set#Card(Map#Domain(m)) } { Map#Card(m) } 
  Set#Card(Map#Domain(m)) == Map#Card(m));

axiom (forall m: Map :: 
  { Set#Card(Map#Values(m)) } { Map#Card(m) } 
  Set#Card(Map#Values(m)) <= Map#Card(m));

axiom (forall m: Map :: 
  { Set#Card(Map#Items(m)) } { Map#Card(m) } 
  Set#Card(Map#Items(m)) == Map#Card(m));

revealed function Map#Values(Map) : Set;

axiom (forall m: Map, v: Box :: 
  { Set#IsMember(Map#Values(m), v) } 
  Set#IsMember(Map#Values(m), v)
     == (exists u: Box :: 
      { Set#IsMember(Map#Domain(m), u) } { Map#Elements(m)[u] } 
      Set#IsMember(Map#Domain(m), u) && v == Map#Elements(m)[u]));

revealed function Map#Items(Map) : Set;

revealed function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

revealed function _System.Tuple2._0(DatatypeType) : Box;

revealed function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map, item: Box :: 
  { Set#IsMember(Map#Items(m), item) } 
  Set#IsMember(Map#Items(m), item)
     <==> Set#IsMember(Map#Domain(m), _System.Tuple2._0($Unbox(item)))
       && Map#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

revealed function Map#Empty() : Map;

axiom (forall u: Box :: 
  { Set#IsMember(Map#Domain(Map#Empty(): Map), u) } 
  !Set#IsMember(Map#Domain(Map#Empty(): Map), u));

revealed function Map#Glue(Set, [Box]Box, Ty) : Map;

axiom (forall a: Set, b: [Box]Box, t: Ty :: 
  { Map#Domain(Map#Glue(a, b, t)) } 
  Map#Domain(Map#Glue(a, b, t)) == a);

axiom (forall a: Set, b: [Box]Box, t: Ty :: 
  { Map#Elements(Map#Glue(a, b, t)) } 
  Map#Elements(Map#Glue(a, b, t)) == b);

axiom (forall a: Set, b: [Box]Box, t0: Ty, t1: Ty :: 
  { Map#Glue(a, b, TMap(t0, t1)) } 
  (forall bx: Box :: Set#IsMember(a, bx) ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
     ==> $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));

revealed function Map#Build(Map, Box, Box) : Map;

axiom (forall m: Map, u: Box, u': Box, v: Box :: 
  { Set#IsMember(Map#Domain(Map#Build(m, u, v)), u') } 
    { Map#Elements(Map#Build(m, u, v))[u'] } 
  (u' == u
       ==> Set#IsMember(Map#Domain(Map#Build(m, u, v)), u')
         && Map#Elements(Map#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> Set#IsMember(Map#Domain(Map#Build(m, u, v)), u')
           == Set#IsMember(Map#Domain(m), u')
         && Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

axiom (forall m: Map, u: Box, v: Box :: 
  { Map#Card(Map#Build(m, u, v)) } 
  Set#IsMember(Map#Domain(m), u) ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

axiom (forall m: Map, u: Box, v: Box :: 
  { Map#Card(Map#Build(m, u, v)) } 
  !Set#IsMember(Map#Domain(m), u)
     ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

revealed function Map#Merge(Map, Map) : Map;

axiom (forall m: Map, n: Map :: 
  { Map#Domain(Map#Merge(m, n)) } 
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));

axiom (forall m: Map, n: Map, u: Box :: 
  { Map#Elements(Map#Merge(m, n))[u] } 
  Set#IsMember(Map#Domain(Map#Merge(m, n)), u)
     ==> (!Set#IsMember(Map#Domain(n), u)
         ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u])
       && (Set#IsMember(Map#Domain(n), u)
         ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

revealed function Map#Subtract(Map, Set) : Map;

axiom (forall m: Map, s: Set :: 
  { Map#Domain(Map#Subtract(m, s)) } 
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));

axiom (forall m: Map, s: Set, u: Box :: 
  { Map#Elements(Map#Subtract(m, s))[u] } 
  Set#IsMember(Map#Domain(Map#Subtract(m, s)), u)
     ==> Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

revealed function Map#Equal(Map, Map) : bool;

axiom (forall m: Map, m': Map :: 
  { Map#Equal(m, m') } 
  Map#Equal(m, m')
     <==> (forall u: Box :: 
        Set#IsMember(Map#Domain(m), u) == Set#IsMember(Map#Domain(m'), u))
       && (forall u: Box :: 
        Set#IsMember(Map#Domain(m), u) ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

axiom (forall m: Map, m': Map :: { Map#Equal(m, m') } Map#Equal(m, m') ==> m == m');

revealed function Map#Disjoint(Map, Map) : bool;

axiom (forall m: Map, m': Map :: 
  { Map#Disjoint(m, m') } 
  Map#Disjoint(m, m')
     <==> (forall o: Box :: 
      { Set#IsMember(Map#Domain(m), o) } { Set#IsMember(Map#Domain(m'), o) } 
      !Set#IsMember(Map#Domain(m), o) || !Set#IsMember(Map#Domain(m'), o)));

type IMap;

revealed function IMap#Domain(IMap) : ISet;

revealed function IMap#Elements(IMap) : [Box]Box;

axiom (forall m: IMap :: 
  { IMap#Domain(m) } 
  m == IMap#Empty() || (exists k: Box :: IMap#Domain(m)[k]));

axiom (forall m: IMap :: 
  { IMap#Values(m) } 
  m == IMap#Empty() || (exists v: Box :: IMap#Values(m)[v]));

axiom (forall m: IMap :: 
  { IMap#Items(m) } 
  m == IMap#Empty()
     || (exists k: Box, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall m: IMap :: 
  { IMap#Domain(m) } 
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());

axiom (forall m: IMap :: 
  { IMap#Values(m) } 
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());

axiom (forall m: IMap :: 
  { IMap#Items(m) } 
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

revealed function IMap#Values(IMap) : ISet;

axiom (forall m: IMap, v: Box :: 
  { IMap#Values(m)[v] } 
  IMap#Values(m)[v]
     == (exists u: Box :: 
      { IMap#Domain(m)[u] } { IMap#Elements(m)[u] } 
      IMap#Domain(m)[u] && v == IMap#Elements(m)[u]));

revealed function IMap#Items(IMap) : ISet;

axiom (forall m: IMap, item: Box :: 
  { IMap#Items(m)[item] } 
  IMap#Items(m)[item]
     <==> IMap#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && IMap#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

revealed function IMap#Empty() : IMap;

axiom (forall u: Box :: 
  { IMap#Domain(IMap#Empty(): IMap)[u] } 
  !IMap#Domain(IMap#Empty(): IMap)[u]);

revealed function IMap#Glue([Box]bool, [Box]Box, Ty) : IMap;

axiom (forall a: [Box]bool, b: [Box]Box, t: Ty :: 
  { IMap#Domain(IMap#Glue(a, b, t)) } 
  IMap#Domain(IMap#Glue(a, b, t)) == a);

axiom (forall a: [Box]bool, b: [Box]Box, t: Ty :: 
  { IMap#Elements(IMap#Glue(a, b, t)) } 
  IMap#Elements(IMap#Glue(a, b, t)) == b);

axiom (forall a: [Box]bool, b: [Box]Box, t0: Ty, t1: Ty :: 
  { IMap#Glue(a, b, TIMap(t0, t1)) } 
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
     ==> $Is(IMap#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

revealed function IMap#Build(IMap, Box, Box) : IMap;

axiom (forall m: IMap, u: Box, u': Box, v: Box :: 
  { IMap#Domain(IMap#Build(m, u, v))[u'] } 
    { IMap#Elements(IMap#Build(m, u, v))[u'] } 
  (u' == u
       ==> IMap#Domain(IMap#Build(m, u, v))[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

revealed function IMap#Equal(IMap, IMap) : bool;

axiom (forall m: IMap, m': IMap :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m')
     <==> (forall u: Box :: IMap#Domain(m)[u] == IMap#Domain(m')[u])
       && (forall u: Box :: 
        IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));

axiom (forall m: IMap, m': IMap :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m') ==> m == m');

revealed function IMap#Merge(IMap, IMap) : IMap;

axiom (forall m: IMap, n: IMap :: 
  { IMap#Domain(IMap#Merge(m, n)) } 
  IMap#Domain(IMap#Merge(m, n)) == ISet#Union(IMap#Domain(m), IMap#Domain(n)));

axiom (forall m: IMap, n: IMap, u: Box :: 
  { IMap#Elements(IMap#Merge(m, n))[u] } 
  IMap#Domain(IMap#Merge(m, n))[u]
     ==> (!IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u])
       && (IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

revealed function IMap#Subtract(IMap, Set) : IMap;

axiom (forall m: IMap, s: Set :: 
  { IMap#Domain(IMap#Subtract(m, s)) } 
  IMap#Domain(IMap#Subtract(m, s))
     == ISet#Difference(IMap#Domain(m), ISet#FromSet(s)));

axiom (forall m: IMap, s: Set, u: Box :: 
  { IMap#Elements(IMap#Subtract(m, s))[u] } 
  IMap#Domain(IMap#Subtract(m, s))[u]
     ==> IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);

revealed function INTERNAL_add_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_add_boogie(x, y): int } 
  INTERNAL_add_boogie(x, y): int == x + y);
}

revealed function INTERNAL_sub_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_sub_boogie(x, y): int } 
  INTERNAL_sub_boogie(x, y): int == x - y);
}

revealed function INTERNAL_mul_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_mul_boogie(x, y): int } 
  INTERNAL_mul_boogie(x, y): int == x * y);
}

revealed function INTERNAL_div_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_div_boogie(x, y): int } 
  INTERNAL_div_boogie(x, y): int == x div y);
}

revealed function INTERNAL_mod_boogie(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: 
  { INTERNAL_mod_boogie(x, y): int } 
  INTERNAL_mod_boogie(x, y): int == x mod y);
}

revealed function {:never_pattern true} INTERNAL_lt_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_lt_boogie(x, y): bool } 
  INTERNAL_lt_boogie(x, y): bool == (x < y));
}

revealed function {:never_pattern true} INTERNAL_le_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_le_boogie(x, y): bool } 
  INTERNAL_le_boogie(x, y): bool == (x <= y));
}

revealed function {:never_pattern true} INTERNAL_gt_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_gt_boogie(x, y): bool } 
  INTERNAL_gt_boogie(x, y): bool == (x > y));
}

revealed function {:never_pattern true} INTERNAL_ge_boogie(x: int, y: int) : bool
uses {
axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_ge_boogie(x, y): bool } 
  INTERNAL_ge_boogie(x, y): bool == (x >= y));
}

revealed function Mul(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Mul(x, y): int } Mul(x, y): int == x * y);
}

revealed function Div(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Div(x, y): int } Div(x, y): int == x div y);
}

revealed function Mod(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Mod(x, y): int } Mod(x, y): int == x mod y);
}

revealed function Add(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Add(x, y): int } Add(x, y): int == x + y);
}

revealed function Sub(x: int, y: int) : int
uses {
axiom (forall x: int, y: int :: { Sub(x, y): int } Sub(x, y): int == x - y);
}

function Tclass._System.nat() : Ty
uses {
// Tclass._System.nat Tag
axiom Tag(Tclass._System.nat()) == Tagclass._System.nat
   && TagFamily(Tclass._System.nat()) == tytagFamily$nat;
}

const unique Tagclass._System.nat: TyTag;

// Box/unbox axiom for Tclass._System.nat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.nat()) } 
  $IsBox(bx, Tclass._System.nat())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._System.nat()));

// $Is axiom for subset type _System.nat
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._System.nat()) } 
  $Is(x#0, Tclass._System.nat()) <==> LitInt(0) <= x#0);

// $IsAlloc axiom for subset type _System.nat
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._System.nat(), $h) } 
  $IsAlloc(x#0, Tclass._System.nat(), $h));

const unique class._System.object?: ClassName;

const unique Tagclass._System.object?: TyTag;

// Box/unbox axiom for Tclass._System.object?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object?()) } 
  $IsBox(bx, Tclass._System.object?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object?()));

// $Is axiom for trait object
axiom (forall $o: ref :: 
  { $Is($o, Tclass._System.object?()) } 
  $Is($o, Tclass._System.object?()));

// $IsAlloc axiom for trait object
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.object?(), $h) } 
  $IsAlloc($o, Tclass._System.object?(), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

function implements$_System.object(ty: Ty) : bool;

function Tclass._System.object() : Ty
uses {
// Tclass._System.object Tag
axiom Tag(Tclass._System.object()) == Tagclass._System.object
   && TagFamily(Tclass._System.object()) == tytagFamily$object;
}

const unique Tagclass._System.object: TyTag;

// Box/unbox axiom for Tclass._System.object
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object()) } 
  $IsBox(bx, Tclass._System.object())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object()));

// $Is axiom for non-null type _System.object
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._System.object()) } { $Is(c#0, Tclass._System.object?()) } 
  $Is(c#0, Tclass._System.object())
     <==> $Is(c#0, Tclass._System.object?()) && c#0 != null);

// $IsAlloc axiom for non-null type _System.object
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.object(), $h) } 
  $IsAlloc(c#0, Tclass._System.object(), $h)
     <==> $IsAlloc(c#0, Tclass._System.object?(), $h));

const unique class._System.array?: ClassName;

function Tclass._System.array?(Ty) : Ty;

const unique Tagclass._System.array?: TyTag;

// Tclass._System.array? Tag
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array?(_System.array$arg) } 
  Tag(Tclass._System.array?(_System.array$arg)) == Tagclass._System.array?
     && TagFamily(Tclass._System.array?(_System.array$arg)) == tytagFamily$array);

function Tclass._System.array?_0(Ty) : Ty;

// Tclass._System.array? injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array?(_System.array$arg) } 
  Tclass._System.array?_0(Tclass._System.array?(_System.array$arg))
     == _System.array$arg);

// Box/unbox axiom for Tclass._System.array?
axiom (forall _System.array$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array?(_System.array$arg)) } 
  $IsBox(bx, Tclass._System.array?(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array?(_System.array$arg)));

// array.: Type axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref, $i0: int :: 
  { read($h, $o, IndexField($i0)), Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && 
      0 <= $i0
       && $i0 < _System.array.Length($o)
     ==> $IsBox(read($h, $o, IndexField($i0)), _System.array$arg));

// array.: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref, $i0: int :: 
  { read($h, $o, IndexField($i0)), Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && 
      0 <= $i0
       && $i0 < _System.array.Length($o)
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAllocBox(read($h, $o, IndexField($i0)), _System.array$arg, $h));

// $Is axiom for array type array
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array?(_System.array$arg)) } 
  $Is($o, Tclass._System.array?(_System.array$arg))
     <==> $o == null || dtype($o) == Tclass._System.array?(_System.array$arg));

// $IsAlloc axiom for array type array
axiom (forall _System.array$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h) } 
  $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

// array.Length: Type axiom
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { _System.array.Length($o), Tclass._System.array?(_System.array$arg) } 
  $o != null && dtype($o) == Tclass._System.array?(_System.array$arg)
     ==> $Is(_System.array.Length($o), TInt));

// array.Length: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array.Length($o), $Unbox(read($h, $o, alloc)): bool, Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc(_System.array.Length($o), TInt, $h));

function Tclass._System.array(Ty) : Ty;

const unique Tagclass._System.array: TyTag;

// Tclass._System.array Tag
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tag(Tclass._System.array(_System.array$arg)) == Tagclass._System.array
     && TagFamily(Tclass._System.array(_System.array$arg)) == tytagFamily$array);

function Tclass._System.array_0(Ty) : Ty;

// Tclass._System.array injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tclass._System.array_0(Tclass._System.array(_System.array$arg))
     == _System.array$arg);

// Box/unbox axiom for Tclass._System.array
axiom (forall _System.array$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array(_System.array$arg)) } 
  $IsBox(bx, Tclass._System.array(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array(_System.array$arg)));

// $Is axiom for non-null type _System.array
axiom (forall _System.array$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array(_System.array$arg)) } 
    { $Is(c#0, Tclass._System.array?(_System.array$arg)) } 
  $Is(c#0, Tclass._System.array(_System.array$arg))
     <==> $Is(c#0, Tclass._System.array?(_System.array$arg)) && c#0 != null);

// $IsAlloc axiom for non-null type _System.array
axiom (forall _System.array$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array(_System.array$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array?(_System.array$arg), $h));

function Tclass._System.___hFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc1: TyTag;

// Tclass._System.___hFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hFunc1(#$T0, #$R)) == Tagclass._System.___hFunc1
     && TagFamily(Tclass._System.___hFunc1(#$T0, #$R)) == tytagFamily$_#Func1);

function Tclass._System.___hFunc1_0(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_0(Tclass._System.___hFunc1(#$T0, #$R)) == #$T0);

function Tclass._System.___hFunc1_1(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_1(Tclass._System.___hFunc1(#$T0, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc1(#$T0, #$R)));

function Handle1([Heap,Box]Box, [Heap,Box]bool, [Heap,Box]Set) : HandleType;

function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;

function Reads1(Ty, Ty, Heap, HandleType, Box) : Set;

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box :: 
  { Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) == h[heap, bx0]);

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box :: 
  { Requires1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  r[heap, bx0] ==> Requires1(t0, t1, heap, Handle1(h, r, rd), bx0));

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set, 
    bx0: Box, 
    bx: Box :: 
  { Set#IsMember(Reads1(t0, t1, heap, Handle1(h, r, rd), bx0), bx) } 
  Set#IsMember(Reads1(t0, t1, heap, Handle1(h, r, rd), bx0), bx)
     == Set#IsMember(rd[heap, bx0], bx));

function {:inline} Requires1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

function {:inline} Reads1#canCall(t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box) : bool
{
  true
}

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Reads1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Reads1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads1(t0, t1, h0, f, bx0) == Reads1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Requires1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Requires1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires1(t0, t1, h0, f, bx0) == Requires1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h0, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// frame axiom for Apply1
axiom (forall t0: Ty, t1: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box :: 
  { $HeapSucc(h0, h1), Apply1(t0, t1, h1, f, bx0) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads1(t0, t1, h1, f, bx0), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// empty-reads property for Reads1 
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Reads1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Reads1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap) && $IsBox(bx0, t0) && $Is(f, Tclass._System.___hFunc1(t0, t1))
     ==> (Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set)
       <==> Set#Equal(Reads1(t0, t1, heap, f, bx0), Set#Empty(): Set)));

// empty-reads property for Requires1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Requires1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Requires1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set)
     ==> Requires1(t0, t1, $OneHeap, f, bx0) == Requires1(t0, t1, heap, f, bx0));

axiom (forall f: HandleType, t0: Ty, t1: Ty :: 
  { $Is(f, Tclass._System.___hFunc1(t0, t1)) } 
  $Is(f, Tclass._System.___hFunc1(t0, t1))
     <==> (forall h: Heap, bx0: Box :: 
      { Apply1(t0, t1, h, f, bx0) } 
      $IsGoodHeap(h) && $IsBox(bx0, t0) && Requires1(t0, t1, h, f, bx0)
         ==> $IsBox(Apply1(t0, t1, h, f, bx0), t1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, u0: Ty, u1: Ty :: 
  { $Is(f, Tclass._System.___hFunc1(t0, t1)), $Is(f, Tclass._System.___hFunc1(u0, u1)) } 
  $Is(f, Tclass._System.___hFunc1(t0, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, t1) } { $IsBox(bx, u1) } 
        $IsBox(bx, t1) ==> $IsBox(bx, u1))
     ==> $Is(f, Tclass._System.___hFunc1(u0, u1)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
       <==> (forall bx0: Box :: 
        { Apply1(t0, t1, h, f, bx0) } { Reads1(t0, t1, h, f, bx0) } 
        $IsBox(bx0, t0) && $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
           ==> (forall r: ref :: 
            { Set#IsMember(Reads1(t0, t1, h, f, bx0), $Box(r)) } 
            r != null && Set#IsMember(Reads1(t0, t1, h, f, bx0), $Box(r))
               ==> $Unbox(read(h, r, alloc)): bool))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc1(t0, t1), h)
     ==> (forall bx0: Box :: 
      { Apply1(t0, t1, h, f, bx0) } 
      $IsAllocBox(bx0, t0, h) && Requires1(t0, t1, h, f, bx0)
         ==> $IsAllocBox(Apply1(t0, t1, h, f, bx0), t1, h)));

function Tclass._System.___hPartialFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc1: TyTag;

// Tclass._System.___hPartialFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hPartialFunc1(#$T0, #$R))
       == Tagclass._System.___hPartialFunc1
     && TagFamily(Tclass._System.___hPartialFunc1(#$T0, #$R))
       == tytagFamily$_#PartialFunc1);

function Tclass._System.___hPartialFunc1_0(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_0(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc1_1(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_1(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc1(#$T0, #$R)));

// $Is axiom for subset type _System._#PartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc1(#$T0, #$R))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0)
           ==> Set#Equal(Reads1(#$T0, #$R, $OneHeap, f#0, x0#0), Set#Empty(): Set)));

// $IsAlloc axiom for subset type _System._#PartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc1(#$T0, #$R), $h));

function Tclass._System.___hTotalFunc1(Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc1: TyTag;

// Tclass._System.___hTotalFunc1 Tag
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tag(Tclass._System.___hTotalFunc1(#$T0, #$R)) == Tagclass._System.___hTotalFunc1
     && TagFamily(Tclass._System.___hTotalFunc1(#$T0, #$R)) == tytagFamily$_#TotalFunc1);

function Tclass._System.___hTotalFunc1_0(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_0(Tclass._System.___hTotalFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc1_1(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_1(Tclass._System.___hTotalFunc1(#$T0, #$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// $Is axioms for subset type _System._#TotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && 
      (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0) ==> Requires1#canCall(#$T0, #$R, $OneHeap, f#0, x0#0))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)));

axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && ((forall x0#0: Box :: 
          $IsBox(x0#0, #$T0) ==> Requires1#canCall(#$T0, #$R, $OneHeap, f#0, x0#0))
         ==> (forall x0#0: Box :: 
          $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)))
     ==> $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// $IsAlloc axiom for subset type _System._#TotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R), $h));

function Tclass._System.___hFunc0(Ty) : Ty;

const unique Tagclass._System.___hFunc0: TyTag;

// Tclass._System.___hFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tag(Tclass._System.___hFunc0(#$R)) == Tagclass._System.___hFunc0
     && TagFamily(Tclass._System.___hFunc0(#$R)) == tytagFamily$_#Func0);

function Tclass._System.___hFunc0_0(Ty) : Ty;

// Tclass._System.___hFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tclass._System.___hFunc0_0(Tclass._System.___hFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc0(#$R)));

function Handle0([Heap]Box, [Heap]bool, [Heap]Set) : HandleType;

function Apply0(Ty, Heap, HandleType) : Box;

function Requires0(Ty, Heap, HandleType) : bool;

function Reads0(Ty, Heap, HandleType) : Set;

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set :: 
  { Apply0(t0, heap, Handle0(h, r, rd)) } 
  Apply0(t0, heap, Handle0(h, r, rd)) == h[heap]);

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set :: 
  { Requires0(t0, heap, Handle0(h, r, rd)) } 
  r[heap] ==> Requires0(t0, heap, Handle0(h, r, rd)));

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set, bx: Box :: 
  { Set#IsMember(Reads0(t0, heap, Handle0(h, r, rd)), bx) } 
  Set#IsMember(Reads0(t0, heap, Handle0(h, r, rd)), bx)
     == Set#IsMember(rd[heap], bx));

function {:inline} Requires0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

function {:inline} Reads0#canCall(t0: Ty, heap: Heap, f: HandleType) : bool
{
  true
}

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h0, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall o: ref, fld: Field :: 
        o != null && Set#IsMember(Reads0(t0, h1, f), $Box(o))
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// empty-reads property for Reads0 
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Reads0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Reads0(t0, heap, f) } 
  $IsGoodHeap(heap) && $Is(f, Tclass._System.___hFunc0(t0))
     ==> (Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set)
       <==> Set#Equal(Reads0(t0, heap, f), Set#Empty(): Set)));

// empty-reads property for Requires0
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Requires0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Requires0(t0, heap, f) } 
  $IsGoodHeap(heap)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set)
     ==> Requires0(t0, $OneHeap, f) == Requires0(t0, heap, f));

axiom (forall f: HandleType, t0: Ty :: 
  { $Is(f, Tclass._System.___hFunc0(t0)) } 
  $Is(f, Tclass._System.___hFunc0(t0))
     <==> (forall h: Heap :: 
      { Apply0(t0, h, f) } 
      $IsGoodHeap(h) && Requires0(t0, h, f) ==> $IsBox(Apply0(t0, h, f), t0)));

axiom (forall f: HandleType, t0: Ty, u0: Ty :: 
  { $Is(f, Tclass._System.___hFunc0(t0)), $Is(f, Tclass._System.___hFunc0(u0)) } 
  $Is(f, Tclass._System.___hFunc0(t0))
       && (forall bx: Box :: 
        { $IsBox(bx, t0) } { $IsBox(bx, u0) } 
        $IsBox(bx, t0) ==> $IsBox(bx, u0))
     ==> $Is(f, Tclass._System.___hFunc0(u0)));

axiom (forall f: HandleType, t0: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc0(t0), h)
       <==> Requires0(t0, h, f)
         ==> (forall r: ref :: 
          { Set#IsMember(Reads0(t0, h, f), $Box(r)) } 
          r != null && Set#IsMember(Reads0(t0, h, f), $Box(r))
             ==> $Unbox(read(h, r, alloc)): bool)));

axiom (forall f: HandleType, t0: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc0(t0), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc0(t0), h)
     ==> 
    Requires0(t0, h, f)
     ==> $IsAllocBox(Apply0(t0, h, f), t0, h));

function Tclass._System.___hPartialFunc0(Ty) : Ty;

const unique Tagclass._System.___hPartialFunc0: TyTag;

// Tclass._System.___hPartialFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tag(Tclass._System.___hPartialFunc0(#$R)) == Tagclass._System.___hPartialFunc0
     && TagFamily(Tclass._System.___hPartialFunc0(#$R)) == tytagFamily$_#PartialFunc0);

function Tclass._System.___hPartialFunc0_0(Ty) : Ty;

// Tclass._System.___hPartialFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tclass._System.___hPartialFunc0_0(Tclass._System.___hPartialFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hPartialFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc0(#$R)));

// $Is axiom for subset type _System._#PartialFunc0
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hFunc0(#$R))
       && Set#Equal(Reads0(#$R, $OneHeap, f#0), Set#Empty(): Set));

// $IsAlloc axiom for subset type _System._#PartialFunc0
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc0(#$R), $h));

function Tclass._System.___hTotalFunc0(Ty) : Ty;

const unique Tagclass._System.___hTotalFunc0: TyTag;

// Tclass._System.___hTotalFunc0 Tag
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tag(Tclass._System.___hTotalFunc0(#$R)) == Tagclass._System.___hTotalFunc0
     && TagFamily(Tclass._System.___hTotalFunc0(#$R)) == tytagFamily$_#TotalFunc0);

function Tclass._System.___hTotalFunc0_0(Ty) : Ty;

// Tclass._System.___hTotalFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tclass._System.___hTotalFunc0_0(Tclass._System.___hTotalFunc0(#$R)) == #$R);

// Box/unbox axiom for Tclass._System.___hTotalFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc0(#$R)));

// $Is axioms for subset type _System._#TotalFunc0
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc0(#$R))
     ==> $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
       && 
      Requires0#canCall(#$R, $OneHeap, f#0)
       && Requires0(#$R, $OneHeap, f#0));

axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
       && (Requires0#canCall(#$R, $OneHeap, f#0) ==> Requires0(#$R, $OneHeap, f#0))
     ==> $Is(f#0, Tclass._System.___hTotalFunc0(#$R)));

// $IsAlloc axiom for subset type _System._#TotalFunc0
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h));

const unique ##_System._tuple#2._#Make2: DtCtorId
uses {
// Constructor identifier
axiom (forall a#0#0#0: Box, a#0#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#0#0#0, a#0#1#0) } 
  DatatypeCtorId(#_System._tuple#2._#Make2(a#0#0#0, a#0#1#0))
     == ##_System._tuple#2._#Make2);
}

function _System.Tuple2.___hMake2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d) } 
  _System.Tuple2.___hMake2_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#2._#Make2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d) } 
  _System.Tuple2.___hMake2_q(d)
     ==> (exists a#1#0#0: Box, a#1#1#0: Box :: 
      d == #_System._tuple#2._#Make2(a#1#0#0, a#1#1#0)));

const unique Tagclass._System.Tuple2: TyTag;

// Tclass._System.Tuple2 Tag
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tag(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
       == Tagclass._System.Tuple2
     && TagFamily(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
       == tytagFamily$_tuple#2);

function Tclass._System.Tuple2_0(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 0
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tclass._System.Tuple2_0(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T0);

function Tclass._System.Tuple2_1(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 1
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tclass._System.Tuple2_1(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T1);

// Box/unbox axiom for Tclass._System.Tuple2
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $IsBox(bx, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)));

// Constructor $Is
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, a#2#0#0: Box, a#2#1#0: Box :: 
  { $Is(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     <==> $IsBox(a#2#0#0, _System._tuple#2$T0) && $IsBox(a#2#1#0, _System._tuple#2$T1));

// Constructor $IsAlloc
axiom (forall _System._tuple#2$T0: Ty, 
    _System._tuple#2$T1: Ty, 
    a#2#0#0: Box, 
    a#2#1#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#2#0#0, a#2#1#0), 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
        $h)
       <==> $IsAllocBox(a#2#0#0, _System._tuple#2$T0, $h)
         && $IsAllocBox(a#2#1#0, _System._tuple#2$T1, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#2$T0: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple2._0(d), _System._tuple#2$T0, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple2.___hMake2_q(d)
       && (exists _System._tuple#2$T1: Ty :: 
        { $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h) } 
        $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._0(d), _System._tuple#2$T0, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _System._tuple#2$T1: Ty, $h: Heap :: 
  { $IsAllocBox(_System.Tuple2._1(d), _System._tuple#2$T1, $h) } 
  $IsGoodHeap($h)
       && 
      _System.Tuple2.___hMake2_q(d)
       && (exists _System._tuple#2$T0: Ty :: 
        { $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h) } 
        $IsAlloc(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), $h))
     ==> $IsAllocBox(_System.Tuple2._1(d), _System._tuple#2$T1, $h));

// Constructor literal
axiom (forall a#3#0#0: Box, a#3#1#0: Box :: 
  { #_System._tuple#2._#Make2(Lit(a#3#0#0), Lit(a#3#1#0)) } 
  #_System._tuple#2._#Make2(Lit(a#3#0#0), Lit(a#3#1#0))
     == Lit(#_System._tuple#2._#Make2(a#3#0#0, a#3#1#0)));

// Constructor injectivity
axiom (forall a#4#0#0: Box, a#4#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#4#0#0, a#4#1#0) } 
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#4#0#0, a#4#1#0)) == a#4#0#0);

// Inductive rank
axiom (forall a#5#0#0: Box, a#5#1#0: Box :: 
  { DtRank(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0)) } 
  BoxRank(a#5#0#0) < DtRank(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0)));

// Constructor injectivity
axiom (forall a#6#0#0: Box, a#6#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0) } 
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)) == a#6#1#0);

// Inductive rank
axiom (forall a#7#0#0: Box, a#7#1#0: Box :: 
  { DtRank(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0)) } 
  BoxRank(a#7#1#0) < DtRank(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0)));

// Depth-one case-split function
function $IsA#_System.Tuple2(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple2(d) } 
  $IsA#_System.Tuple2(d) ==> _System.Tuple2.___hMake2_q(d));

// Questionmark data type disjunctivity
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, d: DatatypeType :: 
  { _System.Tuple2.___hMake2_q(d), $Is(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(d, Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     ==> _System.Tuple2.___hMake2_q(d));

// Datatype extensional equality declaration
function _System.Tuple2#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#2._#Make2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  _System.Tuple2#Equal(a, b)
     <==> _System.Tuple2._0(a) == _System.Tuple2._0(b)
       && _System.Tuple2._1(a) == _System.Tuple2._1(b));

// Datatype extensionality axiom: _System._tuple#2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  _System.Tuple2#Equal(a, b) <==> a == b);

const unique class._System.Tuple2: ClassName;

// Constructor function declaration
function #_System._tuple#0._#Make0() : DatatypeType
uses {
// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;
// Constructor $Is
axiom $Is(#_System._tuple#0._#Make0(), Tclass._System.Tuple0());
// Constructor literal
axiom #_System._tuple#0._#Make0() == Lit(#_System._tuple#0._#Make0());
}

const unique ##_System._tuple#0._#Make0: DtCtorId
uses {
// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;
}

function _System.Tuple0.___hMake0_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d) } 
  _System.Tuple0.___hMake0_q(d)
     <==> DatatypeCtorId(d) == ##_System._tuple#0._#Make0);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d) } 
  _System.Tuple0.___hMake0_q(d) ==> d == #_System._tuple#0._#Make0());

function Tclass._System.Tuple0() : Ty
uses {
// Tclass._System.Tuple0 Tag
axiom Tag(Tclass._System.Tuple0()) == Tagclass._System.Tuple0
   && TagFamily(Tclass._System.Tuple0()) == tytagFamily$_tuple#0;
}

const unique Tagclass._System.Tuple0: TyTag;

// Box/unbox axiom for Tclass._System.Tuple0
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple0()) } 
  $IsBox(bx, Tclass._System.Tuple0())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.Tuple0()));

// Datatype $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(d, Tclass._System.Tuple0(), $h) } 
  $IsGoodHeap($h) && $Is(d, Tclass._System.Tuple0())
     ==> $IsAlloc(d, Tclass._System.Tuple0(), $h));

// Depth-one case-split function
function $IsA#_System.Tuple0(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_System.Tuple0(d) } 
  $IsA#_System.Tuple0(d) ==> _System.Tuple0.___hMake0_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _System.Tuple0.___hMake0_q(d), $Is(d, Tclass._System.Tuple0()) } 
  $Is(d, Tclass._System.Tuple0()) ==> _System.Tuple0.___hMake0_q(d));

// Datatype extensional equality declaration
function _System.Tuple0#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_System._tuple#0._#Make0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  _System.Tuple0#Equal(a, b));

// Datatype extensionality axiom: _System._tuple#0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  _System.Tuple0#Equal(a, b) <==> a == b);

const unique class._System.Tuple0: ClassName;

const unique class._module.__default: ClassName;

// function declaration for _module._default.prime
function _module.__default.prime(n#0: int) : bool;

function _module.__default.prime#canCall(n#0: int) : bool;

function _module.__default.prime#requires(int) : bool;

// #requires axiom for _module.__default.prime
axiom (forall n#0: int :: 
  { _module.__default.prime#requires(n#0) } 
  LitInt(0) <= n#0 ==> _module.__default.prime#requires(n#0) == true);

// #requires ==> #canCall for _module.__default.prime
axiom (forall n#0: int :: 
  { _module.__default.prime#requires(n#0) } 
  _module.__default.prime#requires(n#0) ==> _module.__default.prime#canCall(n#0));

// definition axiom for _module.__default.prime (revealed)
axiom {:id "id0"} (forall n#0: int :: 
  { _module.__default.prime(n#0) } 
  _module.__default.prime#canCall(n#0)
     ==> _module.__default.prime(n#0)
       == (n#0 > 1
         && (forall nr#0: int :: 
          { Mod(n#0, nr#0) } 
          1 < nr#0 && nr#0 < n#0 ==> Mod(n#0, nr#0) != 0)));

// definition axiom for _module.__default.prime for all literals (revealed)
axiom {:id "id1"} (forall n#0: int :: 
  {:weight 3} { _module.__default.prime(LitInt(n#0)) } 
  _module.__default.prime#canCall(LitInt(n#0))
     ==> _module.__default.prime(LitInt(n#0))
       == (n#0 > 1
         && (forall nr#1: int :: 
          { Mod(n#0, nr#1) } 
          1 < nr#1 && nr#1 < n#0 ==> Mod(n#0, nr#1) != 0)));

procedure {:verboseName "prime (well-formedness)"} CheckWellformed$$_module.__default.prime(n#0: int where LitInt(0) <= n#0);
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "prime (well-formedness)"} CheckWellformed$$_module.__default.prime(n#0: int)
{
  var $_ReadsFrame: [ref,Field]bool;
  var nr#2: int;


    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(2,16): initial state"} true;
    $_ReadsFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    // Check well-formedness of preconditions, and then assume them
    // Check well-formedness of the reads clause
    // Check well-formedness of the decreases clause
    // Check body and ensures clauses
    if (*)
    {
        // Check well-formedness of postcondition and assume false
        assume false;
    }
    else
    {
        // Check well-formedness of body and result subset type constraint
        if (n#0 > 1)
        {
            // Begin Comprehension WF check
            havoc nr#2;
            if (true)
            {
                if (1 < nr#2)
                {
                }

                if (1 < nr#2 && nr#2 < n#0)
                {
                    assert {:id "id2"} nr#2 != 0;
                }
            }

            // End Comprehension WF check
            assume true;
        }

        assume true;
        assume {:id "id3"} _module.__default.prime(n#0)
           == (n#0 > 1
             && (forall nr#3: int :: 
              { Mod(n#0, nr#3) } 
              1 < nr#3 && nr#3 < n#0 ==> Mod(n#0, nr#3) != 0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.prime(n#0), TBool);
        return;

        assume false;
    }
}



procedure {:verboseName "testingMethod (well-formedness)"} CheckWellFormed$$_module.__default.testingMethod();
  modifies $Heap;



procedure {:verboseName "testingMethod (call)"} Call$$_module.__default.testingMethod();
  modifies $Heap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "testingMethod (correctness)"} Impl$$_module.__default.testingMethod() returns ($_reverifyPost: bool);
  modifies $Heap;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function Tclass._module.PrimeMap() : Ty
uses {
// Tclass._module.PrimeMap Tag
axiom Tag(Tclass._module.PrimeMap()) == Tagclass._module.PrimeMap
   && TagFamily(Tclass._module.PrimeMap()) == tytagFamily$PrimeMap;
}

const unique Tagclass._module.PrimeMap: TyTag;

// Box/unbox axiom for Tclass._module.PrimeMap
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.PrimeMap()) } 
  $IsBox(bx, Tclass._module.PrimeMap())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.PrimeMap()));

function Tclass._module.Answer() : Ty
uses {
// Tclass._module.Answer Tag
axiom Tag(Tclass._module.Answer()) == Tagclass._module.Answer
   && TagFamily(Tclass._module.Answer()) == tytagFamily$Answer;
}

const unique Tagclass._module.Answer: TyTag;

// Box/unbox axiom for Tclass._module.Answer
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Answer()) } 
  $IsBox(bx, Tclass._module.Answer())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Answer()));

implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "testingMethod (correctness)"} Impl$$_module.__default.testingMethod() returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var nr#0: int;
  var nr#2: int;
  var nr#4: int;
  var defass#pm#0: bool;
  var pm#0: ref
     where defass#pm#0
       ==> $Is(pm#0, Tclass._module.PrimeMap())
         && $IsAlloc(pm#0, Tclass._module.PrimeMap(), $Heap);
  var $nw: ref;
  var n##0: int;
  var n##1: int;
  var n##2: int;
  var result#0: DatatypeType
     where $Is(result#0, Tclass._module.Answer())
       && $IsAlloc(result#0, Tclass._module.Answer(), $Heap);
  var $rhs##0: DatatypeType;
  var n##3: int;
  var result2#0: DatatypeType
     where $Is(result2#0, Tclass._module.Answer())
       && $IsAlloc(result2#0, Tclass._module.Answer(), $Heap);
  var $rhs##1: DatatypeType;
  var n##4: int;
  var result3#0: DatatypeType
     where $Is(result3#0, Tclass._module.Answer())
       && $IsAlloc(result3#0, Tclass._module.Answer(), $Heap);
  var $rhs##2: DatatypeType;
  var n##5: int;
  var result4#0: DatatypeType
     where $Is(result4#0, Tclass._module.Answer())
       && $IsAlloc(result4#0, Tclass._module.Answer(), $Heap);
  var $rhs##3: DatatypeType;
  var n##6: int;

    // AddMethodImpl: testingMethod, Impl$$_module.__default.testingMethod
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(94,23): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(98,3)
    // Begin Comprehension WF check
    havoc nr#0;
    if (true)
    {
        if (1 < nr#0)
        {
        }

        if (1 < nr#0 && nr#0 < 15)
        {
            assert {:id "id4"} {:subsumption 0} nr#0 != 0;
        }
    }

    // End Comprehension WF check
    assume true;
    if (!(forall nr#1: int :: 
      { Mod(15, nr#1) } 
      1 < nr#1 && nr#1 < 15 ==> Mod(15, nr#1) != 0))
    {
        // Begin Comprehension WF check
        havoc nr#2;
        if (true)
        {
            if (1 < nr#2)
            {
            }

            if (1 < nr#2 && nr#2 < 15)
            {
                assert {:id "id5"} {:subsumption 0} nr#2 != 0;
            }
        }

        // End Comprehension WF check
        assume true;
    }

    assume true;
    assert {:id "id6"} {:subsumption 0} !(forall nr#1: int :: 
        { Mod(15, nr#1) } 
        1 < nr#1 && nr#1 < 15 ==> Mod(15, nr#1) != 0)
       ==> (exists nr#3: int :: 
        { Mod(15, nr#3) } 
        1 < nr#3 && nr#3 < 15 && Mod(15, nr#3) == LitInt(0));
    assume {:id "id7"} !(forall nr#1: int :: 
        { Mod(15, nr#1) } 
        1 < nr#1 && nr#1 < 15 ==> Mod(15, nr#1) != 0)
       ==> (exists nr#3: int :: 
        { Mod(15, nr#3) } 
        1 < nr#3 && nr#3 < 15 && Mod(15, nr#3) == LitInt(0));
    // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(99,3)
    assert {:id "id8"} {:subsumption 0} LitInt(3) != 0;
    assume true;
    assert {:id "id9"} LitInt(Mod(15, LitInt(3))) == LitInt(0);
    // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(100,3)
    // Begin Comprehension WF check
    havoc nr#4;
    if (true)
    {
        if (1 < nr#4)
        {
        }

        if (1 < nr#4 && nr#4 < 15)
        {
            assert {:id "id10"} {:subsumption 0} nr#4 != 0;
        }
    }

    // End Comprehension WF check
    assume true;
    assume true;
    assert {:id "id11"} (exists nr#5: int :: 
      { Mod(15, nr#5) } 
      1 < nr#5 && nr#5 < 15 && Mod(15, nr#5) == LitInt(0));
    // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(102,10)
    assume true;
    // ----- init call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(102,13)
    // TrCallStmt: Before ProcessCallStmt
    call {:id "id12"} $nw := Call$$_module.PrimeMap.__ctor();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(102,26)"} true;
    pm#0 := $nw;
    defass#pm#0 := true;
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(102,26)"} true;
    // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(105,17)
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id14"} defass#pm#0;
    assume true;
    assert {:id "id15"} pm#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert {:id "id16"} $Is(LitInt(13), Tclass._System.nat());
    n##0 := LitInt(13);
    assume true;
    assert {:id "id17"} (forall $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool && $o == pm#0
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id18"} Call$$_module.PrimeMap.InsertPrime(pm#0, n##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(105,20)"} true;
    // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(107,18)
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id19"} defass#pm#0;
    assume true;
    assert {:id "id20"} pm#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert {:id "id21"} $Is(LitInt(17), Tclass._System.nat());
    n##1 := LitInt(17);
    assume true;
    assert {:id "id22"} (forall $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool && $o == pm#0
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id23"} Call$$_module.PrimeMap.InsertNumber(pm#0, n##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(107,21)"} true;
    // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(108,18)
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id24"} defass#pm#0;
    assume true;
    assert {:id "id25"} pm#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert {:id "id26"} $Is(LitInt(15), Tclass._System.nat());
    n##2 := LitInt(15);
    assume true;
    assert {:id "id27"} (forall $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool && $o == pm#0
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id28"} Call$$_module.PrimeMap.InsertNumber(pm#0, n##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(108,21)"} true;
    // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(110,3)
    assert {:id "id29"} defass#pm#0;
    assert {:id "id30"} {:subsumption 0} pm#0 != null;
    assume true;
    assume true;
    assume true;
    assert {:id "id31"} Set#Equal(Map#Domain($Unbox(read($Heap, pm#0, _module.PrimeMap.database)): Map), 
      Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set, $Box(LitInt(17))), $Box(LitInt(15))), 
        $Box(LitInt(13))));
    // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(112,36)
    assume true;
    // TrCallStmt: Adding lhs with type Answer
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id32"} defass#pm#0;
    assume true;
    assert {:id "id33"} pm#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert {:id "id34"} $Is(LitInt(17), Tclass._System.nat());
    n##3 := LitInt(17);
    assume true;
    assert {:id "id35"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && Set#IsMember($Unbox(read($Heap, pm#0, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id36"} $rhs##0 := Call$$_module.PrimeMap.IsPrime_q(pm#0, n##3);
    // TrCallStmt: After ProcessCallStmt
    result#0 := $rhs##0;
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(112,39)"} true;
    // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(113,3)
    assume $IsA#_module.Answer(result#0);
    assert {:id "id38"} _module.Answer#Equal(result#0, #_module.Answer.Yes());
    // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(115,37)
    assume true;
    // TrCallStmt: Adding lhs with type Answer
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id39"} defass#pm#0;
    assume true;
    assert {:id "id40"} pm#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert {:id "id41"} $Is(LitInt(15), Tclass._System.nat());
    n##4 := LitInt(15);
    assume true;
    assert {:id "id42"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && Set#IsMember($Unbox(read($Heap, pm#0, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id43"} $rhs##1 := Call$$_module.PrimeMap.IsPrime_q(pm#0, n##4);
    // TrCallStmt: After ProcessCallStmt
    result2#0 := $rhs##1;
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(115,40)"} true;
    // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(116,3)
    assume $IsA#_module.Answer(result2#0);
    assert {:id "id45"} _module.Answer#Equal(result2#0, #_module.Answer.No());
    // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(118,37)
    assume true;
    // TrCallStmt: Adding lhs with type Answer
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id46"} defass#pm#0;
    assume true;
    assert {:id "id47"} pm#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert {:id "id48"} $Is(LitInt(454), Tclass._System.nat());
    n##5 := LitInt(454);
    assume true;
    assert {:id "id49"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && Set#IsMember($Unbox(read($Heap, pm#0, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id50"} $rhs##2 := Call$$_module.PrimeMap.IsPrime_q(pm#0, n##5);
    // TrCallStmt: After ProcessCallStmt
    result3#0 := $rhs##2;
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(118,41)"} true;
    // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(119,3)
    assume $IsA#_module.Answer(result3#0);
    assert {:id "id52"} _module.Answer#Equal(result3#0, #_module.Answer.Unknown());
    // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(121,37)
    assume true;
    // TrCallStmt: Adding lhs with type Answer
    // TrCallStmt: Before ProcessCallStmt
    assert {:id "id53"} defass#pm#0;
    assume true;
    assert {:id "id54"} pm#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert {:id "id55"} $Is(LitInt(13), Tclass._System.nat());
    n##6 := LitInt(13);
    assume true;
    assert {:id "id56"} (forall $o: ref, $f: Field :: 
      $o != null
           && $Unbox(read($Heap, $o, alloc)): bool
           && Set#IsMember($Unbox(read($Heap, pm#0, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $_ModifiesFrame[$o, $f]);
    call {:id "id57"} $rhs##3 := Call$$_module.PrimeMap.IsPrime_q(pm#0, n##6);
    // TrCallStmt: After ProcessCallStmt
    result4#0 := $rhs##3;
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(121,40)"} true;
    // ----- assert statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(122,3)
    assume $IsA#_module.Answer(result4#0);
    assert {:id "id59"} _module.Answer#Equal(result4#0, #_module.Answer.Yes());
}



// Constructor function declaration
function #_module.Answer.Yes() : DatatypeType
uses {
// Constructor identifier
axiom DatatypeCtorId(#_module.Answer.Yes()) == ##_module.Answer.Yes;
// Constructor $Is
axiom $Is(#_module.Answer.Yes(), Tclass._module.Answer());
// Constructor literal
axiom #_module.Answer.Yes() == Lit(#_module.Answer.Yes());
}

const unique ##_module.Answer.Yes: DtCtorId
uses {
// Constructor identifier
axiom DatatypeCtorId(#_module.Answer.Yes()) == ##_module.Answer.Yes;
}

function _module.Answer.Yes_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Answer.Yes_q(d) } 
  _module.Answer.Yes_q(d) <==> DatatypeCtorId(d) == ##_module.Answer.Yes);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Answer.Yes_q(d) } 
  _module.Answer.Yes_q(d) ==> d == #_module.Answer.Yes());

// Constructor function declaration
function #_module.Answer.No() : DatatypeType
uses {
// Constructor identifier
axiom DatatypeCtorId(#_module.Answer.No()) == ##_module.Answer.No;
// Constructor $Is
axiom $Is(#_module.Answer.No(), Tclass._module.Answer());
// Constructor literal
axiom #_module.Answer.No() == Lit(#_module.Answer.No());
}

const unique ##_module.Answer.No: DtCtorId
uses {
// Constructor identifier
axiom DatatypeCtorId(#_module.Answer.No()) == ##_module.Answer.No;
}

function _module.Answer.No_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Answer.No_q(d) } 
  _module.Answer.No_q(d) <==> DatatypeCtorId(d) == ##_module.Answer.No);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Answer.No_q(d) } 
  _module.Answer.No_q(d) ==> d == #_module.Answer.No());

// Constructor function declaration
function #_module.Answer.Unknown() : DatatypeType
uses {
// Constructor identifier
axiom DatatypeCtorId(#_module.Answer.Unknown()) == ##_module.Answer.Unknown;
// Constructor $Is
axiom $Is(#_module.Answer.Unknown(), Tclass._module.Answer());
// Constructor literal
axiom #_module.Answer.Unknown() == Lit(#_module.Answer.Unknown());
}

const unique ##_module.Answer.Unknown: DtCtorId
uses {
// Constructor identifier
axiom DatatypeCtorId(#_module.Answer.Unknown()) == ##_module.Answer.Unknown;
}

function _module.Answer.Unknown_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Answer.Unknown_q(d) } 
  _module.Answer.Unknown_q(d) <==> DatatypeCtorId(d) == ##_module.Answer.Unknown);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Answer.Unknown_q(d) } 
  _module.Answer.Unknown_q(d) ==> d == #_module.Answer.Unknown());

// Datatype $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(d, Tclass._module.Answer(), $h) } 
  $IsGoodHeap($h) && $Is(d, Tclass._module.Answer())
     ==> $IsAlloc(d, Tclass._module.Answer(), $h));

// Depth-one case-split function
function $IsA#_module.Answer(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Answer(d) } 
  $IsA#_module.Answer(d)
     ==> _module.Answer.Yes_q(d) || _module.Answer.No_q(d) || _module.Answer.Unknown_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Answer.Unknown_q(d), $Is(d, Tclass._module.Answer()) } 
    { _module.Answer.No_q(d), $Is(d, Tclass._module.Answer()) } 
    { _module.Answer.Yes_q(d), $Is(d, Tclass._module.Answer()) } 
  $Is(d, Tclass._module.Answer())
     ==> _module.Answer.Yes_q(d) || _module.Answer.No_q(d) || _module.Answer.Unknown_q(d));

// Datatype extensional equality declaration
function _module.Answer#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Answer.Yes
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Answer#Equal(a, b), _module.Answer.Yes_q(a) } 
    { _module.Answer#Equal(a, b), _module.Answer.Yes_q(b) } 
  _module.Answer.Yes_q(a) && _module.Answer.Yes_q(b)
     ==> _module.Answer#Equal(a, b));

// Datatype extensional equality definition: #_module.Answer.No
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Answer#Equal(a, b), _module.Answer.No_q(a) } 
    { _module.Answer#Equal(a, b), _module.Answer.No_q(b) } 
  _module.Answer.No_q(a) && _module.Answer.No_q(b) ==> _module.Answer#Equal(a, b));

// Datatype extensional equality definition: #_module.Answer.Unknown
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Answer#Equal(a, b), _module.Answer.Unknown_q(a) } 
    { _module.Answer#Equal(a, b), _module.Answer.Unknown_q(b) } 
  _module.Answer.Unknown_q(a) && _module.Answer.Unknown_q(b)
     ==> _module.Answer#Equal(a, b));

// Datatype extensionality axiom: _module.Answer
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Answer#Equal(a, b) } 
  _module.Answer#Equal(a, b) <==> a == b);

const unique class._module.Answer: ClassName;

const unique class._module.PrimeMap?: ClassName;

function Tclass._module.PrimeMap?() : Ty
uses {
// Tclass._module.PrimeMap? Tag
axiom Tag(Tclass._module.PrimeMap?()) == Tagclass._module.PrimeMap?
   && TagFamily(Tclass._module.PrimeMap?()) == tytagFamily$PrimeMap;
}

const unique Tagclass._module.PrimeMap?: TyTag;

// Box/unbox axiom for Tclass._module.PrimeMap?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.PrimeMap?()) } 
  $IsBox(bx, Tclass._module.PrimeMap?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.PrimeMap?()));

// $Is axiom for class PrimeMap
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.PrimeMap?()) } 
  $Is($o, Tclass._module.PrimeMap?())
     <==> $o == null || dtype($o) == Tclass._module.PrimeMap?());

// $IsAlloc axiom for class PrimeMap
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.PrimeMap?(), $h) } 
  $IsAlloc($o, Tclass._module.PrimeMap?(), $h)
     <==> $o == null || $Unbox(read($h, $o, alloc)): bool);

const _module.PrimeMap.database: Field
uses {
axiom FDim(_module.PrimeMap.database) == 0
   && FieldOfDecl(class._module.PrimeMap?, field$database)
     == _module.PrimeMap.database
   && !$IsGhostField(_module.PrimeMap.database);
}

// PrimeMap.database: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.PrimeMap.database)): Map } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.PrimeMap?()
     ==> $Is($Unbox(read($h, $o, _module.PrimeMap.database)): Map, 
      TMap(Tclass._System.nat(), TBool)));

// PrimeMap.database: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.PrimeMap.database)): Map } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.PrimeMap?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.PrimeMap.database)): Map, 
      TMap(Tclass._System.nat(), TBool), 
      $h));

// function declaration for _module.PrimeMap.Valid
function _module.PrimeMap.Valid($heap: Heap, this: ref) : bool;

function _module.PrimeMap.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.PrimeMap.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.PrimeMap.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.PrimeMap())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall $o: ref, $f: Field :: 
      $o != null
           && (
            $o == this
             || $o == this
             || Set#IsMember($Unbox(read($h0, this, _module.PrimeMap.Repr)): Set, $Box($o)))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.PrimeMap.Valid($h0, this) == _module.PrimeMap.Valid($h1, this)
       && _module.PrimeMap.Valid#canCall($h0, this)
         == _module.PrimeMap.Valid#canCall($h1, this));

// consequence axiom for _module.PrimeMap.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.PrimeMap.Valid($Heap, this) } 
  _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid#canCall($Heap, this)
       && (_module.PrimeMap.Valid($Heap, this)
         ==> Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))));

function _module.PrimeMap.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.PrimeMap.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.PrimeMap.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.PrimeMap())
       && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap)
     ==> _module.PrimeMap.Valid#requires($Heap, this) == true);

// #requires ==> #canCall for _module.PrimeMap.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.PrimeMap.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  _module.PrimeMap.Valid#requires($Heap, this)
     ==> _module.PrimeMap.Valid#canCall($Heap, this));

// definition axiom for _module.PrimeMap.Valid (revealed)
axiom {:id "id60"} (forall $Heap: Heap, this: ref :: 
  { _module.PrimeMap.Valid($Heap, this), $IsGoodHeap($Heap) } 
  _module.PrimeMap.Valid#canCall($Heap, this)
     ==> (Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
         ==> 
        !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
         ==> (forall i#0: int :: 
          { _module.__default.prime(i#0) } 
            { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)] } 
            { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0)) } 
          LitInt(0) <= i#0
             ==> 
            Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0))
             ==> _module.__default.prime#canCall(i#0)))
       && _module.PrimeMap.Valid($Heap, this)
         == (
          Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
           && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
           && (forall i#0: int :: 
            { _module.__default.prime(i#0) } 
              { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)] } 
              { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0)) } 
            LitInt(0) <= i#0
                 && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0))
               ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)]): bool
                   == Lit(true)
                 <==> _module.__default.prime(i#0)))));

procedure {:verboseName "PrimeMap.Valid (well-formedness)"} CheckWellformed$$_module.PrimeMap.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap));
  modifies $Heap;
  free ensures {:always_assume} this == this || _module.PrimeMap.Valid#canCall($Heap, this);
  ensures {:id "id61"} _module.PrimeMap.Valid($Heap, this)
     ==> Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap.Valid (well-formedness)"} CheckWellformed$$_module.PrimeMap.Valid(this: ref)
{
  var $_ReadsFrame: [ref,Field]bool;
  var b$reqreads#0: bool;
  var newtype$check#0: ref;
  var i#1: int;
  var ##n#0: int;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;

    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(15,18): initial state"} true;
    $_ReadsFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> $o == this
           || $o == this
           || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o)));
    // Check well-formedness of preconditions, and then assume them
    // Check well-formedness of the reads clause
    b$reqreads#0 := $_ReadsFrame[this, _module.PrimeMap.Repr];
    assume true;
    assert {:id "id62"} b$reqreads#0;
    // Check well-formedness of the decreases clause
    assume true;
    // Check body and ensures clauses
    if (*)
    {
        // Check well-formedness of postcondition and assume false
        if (*)
        {
            // assume allocatedness for receiver argument to function
            assume $IsAllocBox($Box(this), Tclass._module.PrimeMap?(), $Heap);
            assume true;
            assert {:id "id63"} this == this
               || (Set#Subset(Set#Union($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, 
                    Set#UnionOne(Set#UnionOne(Set#Empty(): Set, $Box(this)), $Box(this))), 
                  Set#Union($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, 
                    Set#UnionOne(Set#UnionOne(Set#Empty(): Set, $Box(this)), $Box(this))))
                 && !Set#Subset(Set#Union($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, 
                    Set#UnionOne(Set#UnionOne(Set#Empty(): Set, $Box(this)), $Box(this))), 
                  Set#Union($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, 
                    Set#UnionOne(Set#UnionOne(Set#Empty(): Set, $Box(this)), $Box(this)))));
            assume this == this || _module.PrimeMap.Valid#canCall($Heap, this);
            assume {:id "id64"} _module.PrimeMap.Valid($Heap, this);
            assume true;
            assume {:id "id65"} Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
        }
        else
        {
            assume _module.PrimeMap.Valid#canCall($Heap, this);
            assume {:id "id66"} _module.PrimeMap.Valid($Heap, this)
               ==> Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
        }

        assume false;
    }
    else
    {
        // Check well-formedness of body and result subset type constraint
        b$reqreads#1 := $_ReadsFrame[this, _module.PrimeMap.Repr];
        assume true;
        if (Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this)))
        {
            newtype$check#0 := null;
            b$reqreads#2 := $_ReadsFrame[this, _module.PrimeMap.Repr];
            assume true;
        }

        if (Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
           && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null)))
        {
            // Begin Comprehension WF check
            havoc i#1;
            if (LitInt(0) <= i#1)
            {
                b$reqreads#3 := $_ReadsFrame[this, _module.PrimeMap.database];
                assume true;
                assume true;
                if (Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1)))
                {
                    b$reqreads#4 := $_ReadsFrame[this, _module.PrimeMap.database];
                    assume true;
                    assert {:id "id67"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1));
                    ##n#0 := i#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
                    assume _module.__default.prime#canCall(i#1);
                }
            }

            // End Comprehension WF check
            assume (forall i#2: int :: 
              { _module.__default.prime(i#2) } 
                { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)] } 
                { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2)) } 
              LitInt(0) <= i#2
                 ==> 
                Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2))
                 ==> _module.__default.prime#canCall(i#2));
        }

        assume Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
           ==> 
          !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
           ==> (forall i#2: int :: 
            { _module.__default.prime(i#2) } 
              { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)] } 
              { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2)) } 
            LitInt(0) <= i#2
               ==> 
              Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2))
               ==> _module.__default.prime#canCall(i#2));
        assume {:id "id68"} _module.PrimeMap.Valid($Heap, this)
           == (
            Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
             && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
             && (forall i#2: int :: 
              { _module.__default.prime(i#2) } 
                { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)] } 
                { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2)) } 
              LitInt(0) <= i#2
                   && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2))
                 ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)]): bool
                     == Lit(true)
                   <==> _module.__default.prime(i#2))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.PrimeMap.Valid($Heap, this), TBool);
        assert {:id "id69"} b$reqreads#1;
        assert {:id "id70"} b$reqreads#2;
        assert {:id "id71"} b$reqreads#3;
        assert {:id "id72"} b$reqreads#4;
        return;

        assume false;
    }
}



procedure {:verboseName "PrimeMap._ctor (well-formedness)"} CheckWellFormed$$_module.PrimeMap.__ctor() returns (this: ref);
  modifies $Heap;



procedure {:verboseName "PrimeMap._ctor (call)"} Call$$_module.PrimeMap.__ctor()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap));
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  free ensures {:id "id76"} _module.PrimeMap.Valid#canCall($Heap, this)
     && 
    _module.PrimeMap.Valid($Heap, this)
     && 
    Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
     && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
     && (forall i#0: int :: 
      { _module.__default.prime(i#0) } 
        { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)] } 
        { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0)) } 
      LitInt(0) <= i#0
           && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0))
         ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)]): bool
             == Lit(true)
           <==> _module.__default.prime(i#0)));
  free ensures {:always_assume} true;
  ensures {:id "id77"} (forall $o: ref :: 
      { $o != null } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $o != null)
     && (forall $o: ref :: 
      { Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o)) } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
  free ensures {:always_assume} true;
  ensures {:id "id78"} Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, Map#Empty(): Map);
  // constructor allocates the object
  ensures !$Unbox(read(old($Heap), this, alloc)): bool;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "PrimeMap._ctor (correctness)"} Impl$$_module.PrimeMap.__ctor() returns (this: ref, $_reverifyPost: bool);
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  ensures {:id "id79"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
  ensures {:id "id80"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null));
  ensures {:id "id81"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || (forall i#1: int :: 
        { _module.__default.prime(i#1) } 
          { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)] } 
          { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1)) } 
        LitInt(0) <= i#1
             && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1))
           ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)]): bool
               == Lit(true)
             <==> _module.__default.prime(i#1)));
  free ensures {:always_assume} true;
  ensures {:id "id82"} (forall $o: ref :: 
      { $o != null } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $o != null)
     && (forall $o: ref :: 
      { Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o)) } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
  free ensures {:always_assume} true;
  ensures {:id "id83"} Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, Map#Empty(): Map);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap._ctor (correctness)"} Impl$$_module.PrimeMap.__ctor() returns (this: ref, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var this.database: Map;
  var this.Repr: Set;
  var $rhs#0: Set;

    // AddMethodImpl: _ctor, Impl$$_module.PrimeMap.__ctor
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(24,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(24,3)
    // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(25,14)
    assume true;
    assume true;
    assume true;
    this.database := Lit(Map#Empty(): Map);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(25,21)"} true;
    // ----- new; ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(24,3)
    assume this != null && $Is(this, Tclass._module.PrimeMap?());
    assume !$Unbox(read($Heap, this, alloc)): bool;
    assume $Unbox(read($Heap, this, _module.PrimeMap.database)): Map == this.database;
    assume $Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set == this.Repr;
    $Heap := update($Heap, this, alloc, $Box(true));
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(24,3)
    // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(22,3)
    assume true;
    assume true;
    assert {:id "id85"} $_ModifiesFrame[this, _module.PrimeMap.Repr];
    assume true;
    $rhs#0 := Set#UnionOne(Set#Empty(): Set, $Box(this));
    $Heap := update($Heap, this, _module.PrimeMap.Repr, $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(26,2)"} true;
}



procedure {:verboseName "PrimeMap.InsertPrime (well-formedness)"} CheckWellFormed$$_module.PrimeMap.InsertPrime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0);
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap.InsertPrime (well-formedness)"} CheckWellFormed$$_module.PrimeMap.InsertPrime(this: ref, n#0: int)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var ##n#0: int;


    // AddMethodImpl: InsertPrime, CheckWellFormed$$_module.PrimeMap.InsertPrime
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> $o == this);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(29,9): initial state"} true;
    // assume allocatedness for receiver argument to function
    assume $IsAllocBox($Box(this), Tclass._module.PrimeMap?(), $Heap);
    assume _module.PrimeMap.Valid#canCall($Heap, this);
    assume {:id "id88"} _module.PrimeMap.Valid($Heap, this);
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.prime#canCall(n#0);
    assume {:id "id89"} _module.__default.prime(n#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(29,9): post-state"} true;
    // assume allocatedness for receiver argument to function
    assume $IsAllocBox($Box(this), Tclass._module.PrimeMap?(), $Heap);
    assume _module.PrimeMap.Valid#canCall($Heap, this);
    assume {:id "id90"} _module.PrimeMap.Valid($Heap, this);
    assume true;
    assert {:id "id91"} $IsAlloc(this, Tclass._module.PrimeMap(), old($Heap));
    assume true;
    assume {:id "id92"} (forall $o: ref :: 
        { $o != null } 
        Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
             && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
           ==> $o != null)
       && (forall $o: ref :: 
        { $Unbox(read(old($Heap), $o, alloc)): bool } 
        Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
             && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
           ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
    assume true;
    assume true;
    assert {:id "id93"} $IsAlloc(this, Tclass._module.PrimeMap(), old($Heap));
    assume true;
    assert {:id "id94"} $IsAlloc($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map, 
      TMap(Tclass._System.nat(), TBool), 
      old($Heap));
    assume true;
    assume {:id "id95"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
      Set#Union(Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map), 
        Set#UnionOne(Set#Empty(): Set, $Box(n#0))));
    assume true;
    assume true;
    assume {:id "id96"} Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
        $Box(n#0), 
        $Box(Lit(true))));
}



procedure {:verboseName "PrimeMap.InsertPrime (call)"} Call$$_module.PrimeMap.InsertPrime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0);
  // user-defined preconditions
  free requires {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  requires {:id "id97"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
  requires {:id "id98"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null));
  requires {:id "id99"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || (forall i#0: int :: 
        { _module.__default.prime(i#0) } 
          { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)] } 
          { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0)) } 
        LitInt(0) <= i#0
             && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0))
           ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)]): bool
               == Lit(true)
             <==> _module.__default.prime(i#0)));
  free requires {:always_assume} _module.__default.prime#canCall(n#0);
  requires {:id "id100"} _module.__default.prime#canCall(n#0) ==> _module.__default.prime(n#0) || n#0 > 1;
  requires {:id "id101"} _module.__default.prime#canCall(n#0)
     ==> _module.__default.prime(n#0)
       || (forall nr#0: int :: 
        { Mod(n#0, nr#0) } 
        1 < nr#0 && nr#0 < n#0 ==> Mod(n#0, nr#0) != 0);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  free ensures {:id "id102"} _module.PrimeMap.Valid#canCall($Heap, this)
     && 
    _module.PrimeMap.Valid($Heap, this)
     && 
    Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
     && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
     && (forall i#1: int :: 
      { _module.__default.prime(i#1) } 
        { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)] } 
        { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1)) } 
      LitInt(0) <= i#1
           && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1))
         ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)]): bool
             == Lit(true)
           <==> _module.__default.prime(i#1)));
  free ensures {:always_assume} true;
  ensures {:id "id103"} (forall $o: ref :: 
      { $o != null } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $o != null)
     && (forall $o: ref :: 
      { $Unbox(read(old($Heap), $o, alloc)): bool } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
  free ensures {:always_assume} true;
  ensures {:id "id104"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
    Set#Union(Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map), 
      Set#UnionOne(Set#Empty(): Set, $Box(n#0))));
  free ensures {:always_assume} true;
  ensures {:id "id105"} Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
    Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      $Box(n#0), 
      $Box(Lit(true))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "PrimeMap.InsertPrime (correctness)"} Impl$$_module.PrimeMap.InsertPrime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  free requires {:id "id106"} _module.PrimeMap.Valid#canCall($Heap, this)
     && 
    _module.PrimeMap.Valid($Heap, this)
     && 
    Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
     && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
     && (forall i#2: int :: 
      { _module.__default.prime(i#2) } 
        { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)] } 
        { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2)) } 
      LitInt(0) <= i#2
           && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2))
         ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)]): bool
             == Lit(true)
           <==> _module.__default.prime(i#2)));
  free requires {:always_assume} _module.__default.prime#canCall(n#0);
  free requires {:id "id107"} _module.__default.prime#canCall(n#0)
     && 
    _module.__default.prime(n#0)
     && 
    n#0 > 1
     && (forall nr#1: int :: 
      { Mod(n#0, nr#1) } 
      1 < nr#1 && nr#1 < n#0 ==> Mod(n#0, nr#1) != 0);
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  ensures {:id "id108"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
  ensures {:id "id109"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null));
  ensures {:id "id110"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || (forall i#3: int :: 
        { _module.__default.prime(i#3) } 
          { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#3)] } 
          { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#3)) } 
        LitInt(0) <= i#3
             && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#3))
           ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#3)]): bool
               == Lit(true)
             <==> _module.__default.prime(i#3)));
  free ensures {:always_assume} true;
  ensures {:id "id111"} (forall $o: ref :: 
      { $o != null } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $o != null)
     && (forall $o: ref :: 
      { $Unbox(read(old($Heap), $o, alloc)): bool } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
  free ensures {:always_assume} true;
  ensures {:id "id112"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
    Set#Union(Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map), 
      Set#UnionOne(Set#Empty(): Set, $Box(n#0))));
  free ensures {:always_assume} true;
  ensures {:id "id113"} Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
    Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      $Box(n#0), 
      $Box(Lit(true))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap.InsertPrime (correctness)"} Impl$$_module.PrimeMap.InsertPrime(this: ref, n#0: int) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var $rhs#0: Map;

    // AddMethodImpl: InsertPrime, Impl$$_module.PrimeMap.InsertPrime
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> $o == this);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(34,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(35,14)
    assume true;
    assume true;
    assert {:id "id114"} $_ModifiesFrame[this, _module.PrimeMap.database];
    assume true;
    assume true;
    $rhs#0 := Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      $Box(n#0), 
      $Box(Lit(true)));
    $Heap := update($Heap, this, _module.PrimeMap.database, $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(35,35)"} true;
}



procedure {:verboseName "PrimeMap.InsertNumber (well-formedness)"} CheckWellFormed$$_module.PrimeMap.InsertNumber(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0);
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap.InsertNumber (well-formedness)"} CheckWellFormed$$_module.PrimeMap.InsertNumber(this: ref, n#0: int)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var ##n#0: int;
  var ##n#1: int;


    // AddMethodImpl: InsertNumber, CheckWellFormed$$_module.PrimeMap.InsertNumber
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> $o == this);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(39,9): initial state"} true;
    // assume allocatedness for receiver argument to function
    assume $IsAllocBox($Box(this), Tclass._module.PrimeMap?(), $Heap);
    assume _module.PrimeMap.Valid#canCall($Heap, this);
    assume {:id "id117"} _module.PrimeMap.Valid($Heap, this);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(39,9): post-state"} true;
    // assume allocatedness for receiver argument to function
    assume $IsAllocBox($Box(this), Tclass._module.PrimeMap?(), $Heap);
    assume _module.PrimeMap.Valid#canCall($Heap, this);
    assume {:id "id118"} _module.PrimeMap.Valid($Heap, this);
    assume true;
    assert {:id "id119"} $IsAlloc(this, Tclass._module.PrimeMap(), old($Heap));
    assume true;
    assume {:id "id120"} (forall $o: ref :: 
        { $o != null } 
        Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
             && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
           ==> $o != null)
       && (forall $o: ref :: 
        { $Unbox(read(old($Heap), $o, alloc)): bool } 
        Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
             && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
           ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
    assume true;
    assume true;
    assert {:id "id121"} $IsAlloc(this, Tclass._module.PrimeMap(), old($Heap));
    assume true;
    assert {:id "id122"} $IsAlloc($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map, 
      TMap(Tclass._System.nat(), TBool), 
      old($Heap));
    assume true;
    assume {:id "id123"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
      Set#Union(Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map), 
        Set#UnionOne(Set#Empty(): Set, $Box(n#0))));
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.prime#canCall(n#0);
    assume true;
    assume true;
    assume {:id "id124"} _module.__default.prime(n#0)
       <==> Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
        Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
          $Box(n#0), 
          $Box(Lit(true))));
    ##n#1 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    assume _module.__default.prime#canCall(n#0);
    assume true;
    assume true;
    assume {:id "id125"} !_module.__default.prime(n#0)
       <==> Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
        Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
          $Box(n#0), 
          $Box(Lit(false))));
}



procedure {:verboseName "PrimeMap.InsertNumber (call)"} Call$$_module.PrimeMap.InsertNumber(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0);
  // user-defined preconditions
  free requires {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  requires {:id "id126"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
  requires {:id "id127"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null));
  requires {:id "id128"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || (forall i#0: int :: 
        { _module.__default.prime(i#0) } 
          { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)] } 
          { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0)) } 
        LitInt(0) <= i#0
             && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0))
           ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)]): bool
               == Lit(true)
             <==> _module.__default.prime(i#0)));
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  free ensures {:id "id129"} _module.PrimeMap.Valid#canCall($Heap, this)
     && 
    _module.PrimeMap.Valid($Heap, this)
     && 
    Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
     && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
     && (forall i#1: int :: 
      { _module.__default.prime(i#1) } 
        { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)] } 
        { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1)) } 
      LitInt(0) <= i#1
           && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1))
         ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)]): bool
             == Lit(true)
           <==> _module.__default.prime(i#1)));
  free ensures {:always_assume} true;
  ensures {:id "id130"} (forall $o: ref :: 
      { $o != null } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $o != null)
     && (forall $o: ref :: 
      { $Unbox(read(old($Heap), $o, alloc)): bool } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
  free ensures {:always_assume} true;
  ensures {:id "id131"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
    Set#Union(Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map), 
      Set#UnionOne(Set#Empty(): Set, $Box(n#0))));
  free ensures {:always_assume} _module.__default.prime#canCall(n#0);
  ensures {:id "id132"} _module.__default.prime(n#0)
     <==> Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
        $Box(n#0), 
        $Box(Lit(true))));
  free ensures {:always_assume} _module.__default.prime#canCall(n#0);
  ensures {:id "id133"} !_module.__default.prime(n#0)
     <==> Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
        $Box(n#0), 
        $Box(Lit(false))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "PrimeMap.InsertNumber (correctness)"} Impl$$_module.PrimeMap.InsertNumber(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns ($_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  free requires {:id "id134"} _module.PrimeMap.Valid#canCall($Heap, this)
     && 
    _module.PrimeMap.Valid($Heap, this)
     && 
    Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
     && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
     && (forall i#2: int :: 
      { _module.__default.prime(i#2) } 
        { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)] } 
        { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2)) } 
      LitInt(0) <= i#2
           && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2))
         ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)]): bool
             == Lit(true)
           <==> _module.__default.prime(i#2)));
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  ensures {:id "id135"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
  ensures {:id "id136"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null));
  ensures {:id "id137"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || (forall i#3: int :: 
        { _module.__default.prime(i#3) } 
          { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#3)] } 
          { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#3)) } 
        LitInt(0) <= i#3
             && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#3))
           ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#3)]): bool
               == Lit(true)
             <==> _module.__default.prime(i#3)));
  free ensures {:always_assume} true;
  ensures {:id "id138"} (forall $o: ref :: 
      { $o != null } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $o != null)
     && (forall $o: ref :: 
      { $Unbox(read(old($Heap), $o, alloc)): bool } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
  free ensures {:always_assume} true;
  ensures {:id "id139"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
    Set#Union(Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map), 
      Set#UnionOne(Set#Empty(): Set, $Box(n#0))));
  free ensures {:always_assume} _module.__default.prime#canCall(n#0);
  ensures {:id "id140"} _module.__default.prime(n#0)
     <==> Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
        $Box(n#0), 
        $Box(Lit(true))));
  free ensures {:always_assume} _module.__default.prime#canCall(n#0);
  ensures {:id "id141"} !_module.__default.prime(n#0)
     <==> Map#Equal($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
        $Box(n#0), 
        $Box(Lit(false))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap.InsertNumber (correctness)"} Impl$$_module.PrimeMap.InsertNumber(this: ref, n#0: int) returns ($_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var defass#prime#0: bool;
  var prime#0: bool;
  var $rhs##0: bool;
  var n##0: int;
  var $rhs#0: Map;

    // AddMethodImpl: InsertNumber, Impl$$_module.PrimeMap.InsertNumber
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> $o == this);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(44,2): initial state"} true;
    $_reverifyPost := false;
    havoc prime#0;
    // ----- call statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(46,27)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##0 := n#0;
    call {:id "id142"} $rhs##0 := Call$$_module.PrimeMap.testPrimeness(this, n##0);
    // TrCallStmt: After ProcessCallStmt
    prime#0 := $rhs##0;
    defass#prime#0 := true;
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(46,29)"} true;
    // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(47,14)
    assume true;
    assume true;
    assert {:id "id144"} $_ModifiesFrame[this, _module.PrimeMap.database];
    assume true;
    assert {:id "id145"} defass#prime#0;
    assume true;
    $rhs#0 := Map#Build($Unbox(read($Heap, this, _module.PrimeMap.database)): Map, 
      $Box(n#0), 
      $Box(prime#0));
    $Heap := update($Heap, this, _module.PrimeMap.database, $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(47,36)"} true;
}



procedure {:verboseName "PrimeMap.IsPrime? (well-formedness)"} CheckWellFormed$$_module.PrimeMap.IsPrime_q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (answer#0: DatatypeType
       where $Is(answer#0, Tclass._module.Answer())
         && $IsAlloc(answer#0, Tclass._module.Answer(), $Heap));
  modifies $Heap;



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap.IsPrime? (well-formedness)"} CheckWellFormed$$_module.PrimeMap.IsPrime_q(this: ref, n#0: int) returns (answer#0: DatatypeType)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var ##n#0: int;
  var ##n#1: int;


    // AddMethodImpl: IsPrime?, CheckWellFormed$$_module.PrimeMap.IsPrime_q
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o)));
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(52,9): initial state"} true;
    // assume allocatedness for receiver argument to function
    assume $IsAllocBox($Box(this), Tclass._module.PrimeMap?(), $Heap);
    assume _module.PrimeMap.Valid#canCall($Heap, this);
    assume {:id "id148"} _module.PrimeMap.Valid($Heap, this);
    assume true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
         ==> $Heap[$o] == old($Heap)[$o]
           || Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o)));
    assume $HeapSucc(old($Heap), $Heap);
    havoc answer#0;
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(52,9): post-state"} true;
    // assume allocatedness for receiver argument to function
    assume $IsAllocBox($Box(this), Tclass._module.PrimeMap?(), $Heap);
    assume _module.PrimeMap.Valid#canCall($Heap, this);
    assume {:id "id149"} _module.PrimeMap.Valid($Heap, this);
    assume true;
    assert {:id "id150"} $IsAlloc(this, Tclass._module.PrimeMap(), old($Heap));
    assume true;
    assume {:id "id151"} (forall $o: ref :: 
        { $o != null } 
        Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
             && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
           ==> $o != null)
       && (forall $o: ref :: 
        { $Unbox(read(old($Heap), $o, alloc)): bool } 
        Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
             && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
           ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
    assume true;
    assume true;
    assert {:id "id152"} $IsAlloc(this, Tclass._module.PrimeMap(), old($Heap));
    assume true;
    assert {:id "id153"} $IsAlloc($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map, 
      TMap(Tclass._System.nat(), TBool), 
      old($Heap));
    assume true;
    assume {:id "id154"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
      Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map));
    assume true;
    if (Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0)))
    {
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assume _module.__default.prime#canCall(n#0);
    }

    assume {:id "id155"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
         && _module.__default.prime(n#0)
       <==> _module.Answer#Equal(answer#0, #_module.Answer.Yes());
    assume true;
    if (Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0)))
    {
        ##n#1 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
        assume _module.__default.prime#canCall(n#0);
    }

    assume {:id "id156"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
         && !_module.__default.prime(n#0)
       <==> _module.Answer#Equal(answer#0, #_module.Answer.No());
    assume true;
    assume {:id "id157"} !Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       <==> _module.Answer#Equal(answer#0, #_module.Answer.Unknown());
}



procedure {:verboseName "PrimeMap.IsPrime? (call)"} Call$$_module.PrimeMap.IsPrime_q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (answer#0: DatatypeType
       where $Is(answer#0, Tclass._module.Answer())
         && $IsAlloc(answer#0, Tclass._module.Answer(), $Heap));
  // user-defined preconditions
  free requires {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  requires {:id "id158"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
  requires {:id "id159"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null));
  requires {:id "id160"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || (forall i#0: int :: 
        { _module.__default.prime(i#0) } 
          { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)] } 
          { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0)) } 
        LitInt(0) <= i#0
             && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0))
           ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)]): bool
               == Lit(true)
             <==> _module.__default.prime(i#0)));
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  free ensures {:id "id161"} _module.PrimeMap.Valid#canCall($Heap, this)
     && 
    _module.PrimeMap.Valid($Heap, this)
     && 
    Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
     && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
     && (forall i#1: int :: 
      { _module.__default.prime(i#1) } 
        { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)] } 
        { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1)) } 
      LitInt(0) <= i#1
           && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1))
         ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)]): bool
             == Lit(true)
           <==> _module.__default.prime(i#1)));
  free ensures {:always_assume} true;
  ensures {:id "id162"} (forall $o: ref :: 
      { $o != null } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $o != null)
     && (forall $o: ref :: 
      { $Unbox(read(old($Heap), $o, alloc)): bool } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
  free ensures {:always_assume} true;
  ensures {:id "id163"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
    Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map));
  free ensures {:always_assume} (Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       ==> _module.__default.prime#canCall(n#0))
     && $IsA#_module.Answer(answer#0);
  ensures {:id "id164"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       && _module.__default.prime(n#0)
     <==> _module.Answer#Equal(answer#0, #_module.Answer.Yes());
  free ensures {:always_assume} (Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       ==> _module.__default.prime#canCall(n#0))
     && $IsA#_module.Answer(answer#0);
  ensures {:id "id165"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       && !_module.__default.prime(n#0)
     <==> _module.Answer#Equal(answer#0, #_module.Answer.No());
  free ensures {:always_assume} $IsA#_module.Answer(answer#0);
  ensures {:id "id166"} !Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
     <==> _module.Answer#Equal(answer#0, #_module.Answer.Unknown());
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o)));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "PrimeMap.IsPrime? (correctness)"} Impl$$_module.PrimeMap.IsPrime_q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (defass#answer#0: bool, 
    answer#0: DatatypeType
       where defass#answer#0
         ==> $Is(answer#0, Tclass._module.Answer())
           && $IsAlloc(answer#0, Tclass._module.Answer(), $Heap), 
    $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  free requires {:id "id167"} _module.PrimeMap.Valid#canCall($Heap, this)
     && 
    _module.PrimeMap.Valid($Heap, this)
     && 
    Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
     && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
     && (forall i#2: int :: 
      { _module.__default.prime(i#2) } 
        { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)] } 
        { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2)) } 
      LitInt(0) <= i#2
           && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#2))
         ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#2)]): bool
             == Lit(true)
           <==> _module.__default.prime(i#2)));
  // user-defined frame expressions
  free requires {:always_assume} true;
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  ensures {:id "id168"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
  ensures {:id "id169"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null));
  ensures {:id "id170"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || (forall i#3: int :: 
        { _module.__default.prime(i#3) } 
          { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#3)] } 
          { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#3)) } 
        LitInt(0) <= i#3
             && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#3))
           ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#3)]): bool
               == Lit(true)
             <==> _module.__default.prime(i#3)));
  free ensures {:always_assume} true;
  ensures {:id "id171"} (forall $o: ref :: 
      { $o != null } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> $o != null)
     && (forall $o: ref :: 
      { $Unbox(read(old($Heap), $o, alloc)): bool } 
      Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o))
           && !Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o))
         ==> !$Unbox(read(old($Heap), $o, alloc)): bool);
  free ensures {:always_assume} true;
  ensures {:id "id172"} Set#Equal(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), 
    Map#Domain($Unbox(read(old($Heap), this, _module.PrimeMap.database)): Map));
  free ensures {:always_assume} (Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       ==> _module.__default.prime#canCall(n#0))
     && $IsA#_module.Answer(answer#0);
  ensures {:id "id173"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       && _module.__default.prime(n#0)
     <==> _module.Answer#Equal(answer#0, #_module.Answer.Yes());
  free ensures {:always_assume} (Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       ==> _module.__default.prime#canCall(n#0))
     && $IsA#_module.Answer(answer#0);
  ensures {:id "id174"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
       && !_module.__default.prime(n#0)
     <==> _module.Answer#Equal(answer#0, #_module.Answer.No());
  free ensures {:always_assume} $IsA#_module.Answer(answer#0);
  ensures {:id "id175"} !Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0))
     <==> _module.Answer#Equal(answer#0, #_module.Answer.Unknown());
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]
         || Set#IsMember($Unbox(read(old($Heap), this, _module.PrimeMap.Repr)): Set, $Box($o)));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap.IsPrime? (correctness)"} Impl$$_module.PrimeMap.IsPrime_q(this: ref, n#0: int)
   returns (defass#answer#0: bool, answer#0: DatatypeType, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;

    // AddMethodImpl: IsPrime?, Impl$$_module.PrimeMap.IsPrime_q
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool
         ==> Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box($o)));
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(57,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(58,5)
    assume true;
    assume true;
    if (!Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0)))
    {
        // ----- return statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(59,7)
        // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(59,7)
        assume true;
        assume true;
        answer#0 := Lit(#_module.Answer.Unknown());
        defass#answer#0 := true;
        assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(59,20)"} true;
        assert {:id "id177"} defass#answer#0;
        return;
    }
    else
    {
        // ----- if statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(60,12)
        assume true;
        assert {:id "id178"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0));
        assume true;
        if ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(n#0)]): bool
           == Lit(true))
        {
            // ----- return statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(61,7)
            // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(61,7)
            assume true;
            assume true;
            answer#0 := Lit(#_module.Answer.Yes());
            defass#answer#0 := true;
            assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(61,16)"} true;
            assert {:id "id180"} defass#answer#0;
            return;
        }
        else
        {
            // ----- if statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(62,12)
            assume true;
            assert {:id "id181"} Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(n#0));
            assume true;
            if ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(n#0)]): bool
               == Lit(false))
            {
                // ----- return statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(63,7)
                // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(63,7)
                assume true;
                assume true;
                answer#0 := Lit(#_module.Answer.No());
                defass#answer#0 := true;
                assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(63,15)"} true;
                assert {:id "id183"} defass#answer#0;
                return;
            }
            else
            {
            }
        }
    }

    assert {:id "id184"} defass#answer#0;
}



procedure {:verboseName "PrimeMap.testPrimeness (well-formedness)"} CheckWellFormed$$_module.PrimeMap.testPrimeness(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (result#0: bool);
  modifies $Heap;



procedure {:verboseName "PrimeMap.testPrimeness (call)"} Call$$_module.PrimeMap.testPrimeness(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (result#0: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  requires {:id "id188"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this));
  requires {:id "id189"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null));
  requires {:id "id190"} _module.PrimeMap.Valid#canCall($Heap, this)
     ==> _module.PrimeMap.Valid($Heap, this)
       || (forall i#0: int :: 
        { _module.__default.prime(i#0) } 
          { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)] } 
          { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0)) } 
        LitInt(0) <= i#0
             && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#0))
           ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#0)]): bool
               == Lit(true)
             <==> _module.__default.prime(i#0)));
  free requires {:always_assume} true;
  requires {:id "id191"} n#0 >= LitInt(0);
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.__default.prime#canCall(n#0);
  ensures {:id "id192"} result#0 <==> _module.__default.prime(n#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verboseName "PrimeMap.testPrimeness (correctness)"} Impl$$_module.PrimeMap.testPrimeness(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.PrimeMap())
         && $IsAlloc(this, Tclass._module.PrimeMap(), $Heap), 
    n#0: int where LitInt(0) <= n#0)
   returns (defass#result#0: bool, result#0: bool, $_reverifyPost: bool);
  // user-defined preconditions
  free requires {:always_assume} _module.PrimeMap.Valid#canCall($Heap, this);
  free requires {:id "id193"} _module.PrimeMap.Valid#canCall($Heap, this)
     && 
    _module.PrimeMap.Valid($Heap, this)
     && 
    Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(this))
     && !Set#IsMember($Unbox(read($Heap, this, _module.PrimeMap.Repr)): Set, $Box(null))
     && (forall i#1: int :: 
      { _module.__default.prime(i#1) } 
        { Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)] } 
        { Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1)) } 
      LitInt(0) <= i#1
           && Set#IsMember(Map#Domain($Unbox(read($Heap, this, _module.PrimeMap.database)): Map), $Box(i#1))
         ==> ($Unbox(Map#Elements($Unbox(read($Heap, this, _module.PrimeMap.database)): Map)[$Box(i#1)]): bool
             == Lit(true)
           <==> _module.__default.prime(i#1)));
  free requires {:always_assume} true;
  requires {:id "id194"} n#0 >= LitInt(0);
  modifies $Heap;
  // user-defined postconditions
  free ensures {:always_assume} _module.__default.prime#canCall(n#0);
  ensures {:id "id195"} result#0 <==> _module.__default.prime(n#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
       ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:smt_option "smt.arith.solver", "2"} {:verboseName "PrimeMap.testPrimeness (correctness)"} Impl$$_module.PrimeMap.testPrimeness(this: ref, n#0: int)
   returns (defass#result#0: bool, result#0: bool, $_reverifyPost: bool)
{
  var $_ModifiesFrame: [ref,Field]bool;
  var i#2: int;
  var $PreLoopHeap$loop#0: Heap;
  var preLoop$loop#0$defass#result#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var j#0: int;
  var $decr$loop#00: int;

    // AddMethodImpl: testPrimeness, Impl$$_module.PrimeMap.testPrimeness
    $_ModifiesFrame := (lambda $o: ref, $f: Field :: 
      $o != null && $Unbox(read($Heap, $o, alloc)): bool ==> false);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(73,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(74,4)
    if (n#0 != LitInt(0))
    {
    }

    assume true;
    if (n#0 == LitInt(0) || n#0 == LitInt(1))
    {
        push;
        // ----- return statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(75,5)
        // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(75,5)
        assume true;
        assume true;
        result#0 := Lit(false);
        defass#result#0 := true;
        assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(75,16)"} true;
        assert {:id "id197"} defass#result#0;
        pop;
        return;

        pop;
    }
    else
    {
    }

    // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(77,11)
    assume true;
    assume true;
    i#2 := LitInt(2);
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(77,14)"} true;
    // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(78,12)
    assume true;
    assume true;
    result#0 := Lit(true);
    defass#result#0 := true;
    assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(78,18)"} true;
    // ----- while statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(80,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#result#0 := defass#result#0;
    $decr_init$loop#00 := n#0 - i#2;
    havoc $w$loop#0;
    assume true;
    assume true;
    assume $w$loop#0 ==> true;
    while (true)
      free invariant true;
      invariant {:id "id201"} $w$loop#0 ==> i#2 <= n#0;
      free invariant true;
      invariant {:id "id205"} $w$loop#0
         ==> (result#0
           <==> (forall j#1: int :: 
            { Mod(n#0, j#1) } 
            1 < j#1 && j#1 <= i#2 - 1 ==> Mod(n#0, j#1) != 0));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && $Unbox(read(old($Heap), $o, alloc)): bool
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall $o: ref, $f: Field :: 
        { read($Heap, $o, $f) } 
        $o != null && $Unbox(read($PreLoopHeap$loop#0, $o, alloc)): bool
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
             || $_ModifiesFrame[$o, $f]);
      free invariant preLoop$loop#0$defass#result#0 ==> defass#result#0;
      free invariant n#0 - i#2 <= $decr_init$loop#00;
    {
        assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(80,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume {:id "id200"} i#2 <= n#0;
            assert {:id "id202"} defass#result#0;
            // Begin Comprehension WF check
            havoc j#0;
            if (true)
            {
                if (1 < j#0)
                {
                }

                if (1 < j#0 && j#0 <= i#2 - 1)
                {
                    assert {:id "id203"} {:subsumption 0} j#0 != 0;
                }
            }

            // End Comprehension WF check
            assume true;
            assume true;
            assume {:id "id204"} result#0
               <==> (forall j#1: int :: 
                { Mod(n#0, j#1) } 
                1 < j#1 && j#1 <= i#2 - 1 ==> Mod(n#0, j#1) != 0);
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#2)
        {
            break;
        }

        assume true;
        $decr$loop#00 := n#0 - i#2;
        // ----- if statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(86,7)
        assert {:id "id206"} i#2 != 0;
        assume true;
        if (Mod(n#0, i#2) == LitInt(0))
        {
            push;
            // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(87,16)
            assume true;
            assume true;
            result#0 := Lit(false);
            defass#result#0 := true;
            assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(87,23)"} true;
            pop;
        }
        else
        {
        }

        // ----- assignment statement ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(89,9)
        assume true;
        assume true;
        i#2 := i#2 + 1;
        assume {:captureState "DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(89,16)"} true;
        assume true;
        // ----- loop termination check ----- /home/ricostynha/Desktop/drive/ProjectBase/projects/drive.ProjectBase/code/ProofPulse/dataset/dafny_dataset_files/DafnyPrograms_tmp_tmp74_f9k_c_prime-database.dfy(80,5)
        assert {:id "id209"} 0 <= $decr$loop#00 || n#0 - i#2 == $decr$loop#00;
        assert {:id "id210"} n#0 - i#2 < $decr$loop#00;
        assume true;
    }

    assert {:id "id211"} defass#result#0;
}



const _module.PrimeMap.Repr: Field
uses {
axiom FDim(_module.PrimeMap.Repr) == 0
   && FieldOfDecl(class._module.PrimeMap?, field$Repr) == _module.PrimeMap.Repr
   && $IsGhostField(_module.PrimeMap.Repr);
}

// PrimeMap.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.PrimeMap.Repr)): Set } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.PrimeMap?()
     ==> $Is($Unbox(read($h, $o, _module.PrimeMap.Repr)): Set, TSet(Tclass._System.object?())));

// PrimeMap.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { $Unbox(read($h, $o, _module.PrimeMap.Repr)): Set } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.PrimeMap?()
       && $Unbox(read($h, $o, alloc)): bool
     ==> $IsAlloc($Unbox(read($h, $o, _module.PrimeMap.Repr)): Set, 
      TSet(Tclass._System.object?()), 
      $h));

// $Is axiom for non-null type _module.PrimeMap
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.PrimeMap()) } 
    { $Is(c#0, Tclass._module.PrimeMap?()) } 
  $Is(c#0, Tclass._module.PrimeMap())
     <==> $Is(c#0, Tclass._module.PrimeMap?()) && c#0 != null);

// $IsAlloc axiom for non-null type _module.PrimeMap
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.PrimeMap(), $h) } 
  $IsAlloc(c#0, Tclass._module.PrimeMap(), $h)
     <==> $IsAlloc(c#0, Tclass._module.PrimeMap?(), $h));

const unique tytagFamily$nat: TyTagFamily;

const unique tytagFamily$object: TyTagFamily;

const unique tytagFamily$array: TyTagFamily;

const unique tytagFamily$_#Func1: TyTagFamily;

const unique tytagFamily$_#PartialFunc1: TyTagFamily;

const unique tytagFamily$_#TotalFunc1: TyTagFamily;

const unique tytagFamily$_#Func0: TyTagFamily;

const unique tytagFamily$_#PartialFunc0: TyTagFamily;

const unique tytagFamily$_#TotalFunc0: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$PrimeMap: TyTagFamily;

const unique tytagFamily$Answer: TyTagFamily;

const unique field$database: NameFamily;

const unique field$Repr: NameFamily;
