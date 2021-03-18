// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy -print:./DefiniteAssignment.bpl

type Ty;

type TyTag;

type TyTagFamily;

type char;

type ref;

type Box;

type ClassName;

type HandleType;

type DatatypeType;

type DtCtorId;

type LayerType;

type Field _;

type NameFamily;

type TickType;

type Seq _;

type Map _ _;

type IMap _ _;

const $$Language$Dafny: bool;

axiom $$Language$Dafny;

type Bv0 = int;

const unique TBool: Ty;

const unique TChar: Ty;

const unique TInt: Ty;

const unique TReal: Ty;

const unique TORDINAL: Ty;

function TBitvector(int) : Ty;

function TSet(Ty) : Ty;

function TISet(Ty) : Ty;

function TMultiSet(Ty) : Ty;

function TSeq(Ty) : Ty;

function TMap(Ty, Ty) : Ty;

function TIMap(Ty, Ty) : Ty;

function Inv0_TBitvector(Ty) : int;

axiom (forall w: int :: { TBitvector(w) } Inv0_TBitvector(TBitvector(w)) == w);

function Inv0_TSet(Ty) : Ty;

axiom (forall t: Ty :: { TSet(t) } Inv0_TSet(TSet(t)) == t);

function Inv0_TISet(Ty) : Ty;

axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);

function Inv0_TSeq(Ty) : Ty;

axiom (forall t: Ty :: { TSeq(t) } Inv0_TSeq(TSeq(t)) == t);

function Inv0_TMultiSet(Ty) : Ty;

axiom (forall t: Ty :: { TMultiSet(t) } Inv0_TMultiSet(TMultiSet(t)) == t);

function Inv0_TMap(Ty) : Ty;

function Inv1_TMap(Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv0_TMap(TMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Inv1_TMap(TMap(t, u)) == u);

function Inv0_TIMap(Ty) : Ty;

function Inv1_TIMap(Ty) : Ty;

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv0_TIMap(TIMap(t, u)) == t);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Inv1_TIMap(TIMap(t, u)) == u);

function Tag(Ty) : TyTag;

const unique TagBool: TyTag;

const unique TagChar: TyTag;

const unique TagInt: TyTag;

const unique TagReal: TyTag;

const unique TagORDINAL: TyTag;

const unique TagSet: TyTag;

const unique TagISet: TyTag;

const unique TagMultiSet: TyTag;

const unique TagSeq: TyTag;

const unique TagMap: TyTag;

const unique TagIMap: TyTag;

const unique TagClass: TyTag;

axiom Tag(TBool) == TagBool;

axiom Tag(TChar) == TagChar;

axiom Tag(TInt) == TagInt;

axiom Tag(TReal) == TagReal;

axiom Tag(TORDINAL) == TagORDINAL;

axiom (forall t: Ty :: { TSet(t) } Tag(TSet(t)) == TagSet);

axiom (forall t: Ty :: { TISet(t) } Tag(TISet(t)) == TagISet);

axiom (forall t: Ty :: { TMultiSet(t) } Tag(TMultiSet(t)) == TagMultiSet);

axiom (forall t: Ty :: { TSeq(t) } Tag(TSeq(t)) == TagSeq);

axiom (forall t: Ty, u: Ty :: { TMap(t, u) } Tag(TMap(t, u)) == TagMap);

axiom (forall t: Ty, u: Ty :: { TIMap(t, u) } Tag(TIMap(t, u)) == TagIMap);

function TagFamily(Ty) : TyTagFamily;

function {:identity} Lit<T>(x: T) : T;

axiom (forall<T> x: T :: {:identity} { Lit(x): T } Lit(x): T == x);

axiom (forall<T> x: T :: { $Box(Lit(x)) } $Box(Lit(x)) == Lit($Box(x)));

function {:identity} LitInt(x: int) : int;

axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);

axiom (forall x: int :: { $Box(LitInt(x)) } $Box(LitInt(x)) == Lit($Box(x)));

function {:identity} LitReal(x: real) : real;

axiom (forall x: real :: {:identity} { LitReal(x): real } LitReal(x): real == x);

axiom (forall x: real :: { $Box(LitReal(x)) } $Box(LitReal(x)) == Lit($Box(x)));

function char#FromInt(int) : char;

function char#ToInt(char) : int;

axiom (forall ch: char :: 
  { char#ToInt(ch) } 
  char#FromInt(char#ToInt(ch)) == ch
     && 0 <= char#ToInt(ch)
     && char#ToInt(ch) < 65536);

axiom (forall n: int :: 
  { char#FromInt(n) } 
  0 <= n && n < 65536 ==> char#ToInt(char#FromInt(n)) == n);

function char#Plus(char, char) : char;

function char#Minus(char, char) : char;

axiom (forall a: char, b: char :: 
  { char#Plus(a, b) } 
  char#Plus(a, b) == char#FromInt(char#ToInt(a) + char#ToInt(b)));

axiom (forall a: char, b: char :: 
  { char#Minus(a, b) } 
  char#Minus(a, b) == char#FromInt(char#ToInt(a) - char#ToInt(b)));

const null: ref;

const $ArbitraryBoxValue: Box;

function $Box<T>(T) : Box;

function $Unbox<T>(Box) : T;

axiom (forall<T> x: T :: { $Box(x) } $Unbox($Box(x)) == x);

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
     ==> $Box($Unbox(bx): Bv0) == bx && $Is($Unbox(bx): Set Box, TBitvector(0)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSet(t)) } 
  $IsBox(bx, TSet(t))
     ==> $Box($Unbox(bx): Set Box) == bx && $Is($Unbox(bx): Set Box, TSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TISet(t)) } 
  $IsBox(bx, TISet(t))
     ==> $Box($Unbox(bx): ISet Box) == bx && $Is($Unbox(bx): ISet Box, TISet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TMultiSet(t)) } 
  $IsBox(bx, TMultiSet(t))
     ==> $Box($Unbox(bx): MultiSet Box) == bx
       && $Is($Unbox(bx): MultiSet Box, TMultiSet(t)));

axiom (forall bx: Box, t: Ty :: 
  { $IsBox(bx, TSeq(t)) } 
  $IsBox(bx, TSeq(t))
     ==> $Box($Unbox(bx): Seq Box) == bx && $Is($Unbox(bx): Seq Box, TSeq(t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TMap(s, t)) } 
  $IsBox(bx, TMap(s, t))
     ==> $Box($Unbox(bx): Map Box Box) == bx && $Is($Unbox(bx): Map Box Box, TMap(s, t)));

axiom (forall bx: Box, s: Ty, t: Ty :: 
  { $IsBox(bx, TIMap(s, t)) } 
  $IsBox(bx, TIMap(s, t))
     ==> $Box($Unbox(bx): IMap Box Box) == bx
       && $Is($Unbox(bx): IMap Box Box, TIMap(s, t)));

axiom (forall<T> v: T, t: Ty :: 
  { $IsBox($Box(v), t) } 
  $IsBox($Box(v), t) <==> $Is(v, t));

axiom (forall<T> v: T, t: Ty, h: Heap :: 
  { $IsAllocBox($Box(v), t, h) } 
  $IsAllocBox($Box(v), t, h) <==> $IsAlloc(v, t, h));

function $Is<T>(T, Ty) : bool;

function $IsAlloc<T>(T, Ty, Heap) : bool;

function $IsBox<T>(T, Ty) : bool;

function $IsAllocBox<T>(T, Ty, Heap) : bool;

axiom (forall v: int :: { $Is(v, TInt) } $Is(v, TInt));

axiom (forall v: real :: { $Is(v, TReal) } $Is(v, TReal));

axiom (forall v: bool :: { $Is(v, TBool) } $Is(v, TBool));

axiom (forall v: char :: { $Is(v, TChar) } $Is(v, TChar));

axiom (forall v: ORDINAL :: { $Is(v, TORDINAL) } $Is(v, TORDINAL));

axiom (forall h: Heap, v: int :: { $IsAlloc(v, TInt, h) } $IsAlloc(v, TInt, h));

axiom (forall h: Heap, v: real :: { $IsAlloc(v, TReal, h) } $IsAlloc(v, TReal, h));

axiom (forall h: Heap, v: bool :: { $IsAlloc(v, TBool, h) } $IsAlloc(v, TBool, h));

axiom (forall h: Heap, v: char :: { $IsAlloc(v, TChar, h) } $IsAlloc(v, TChar, h));

axiom (forall h: Heap, v: ORDINAL :: 
  { $IsAlloc(v, TORDINAL, h) } 
  $IsAlloc(v, TORDINAL, h));

axiom (forall v: Bv0 :: { $Is(v, TBitvector(0)) } $Is(v, TBitvector(0)));

axiom (forall v: Bv0, h: Heap :: 
  { $IsAlloc(v, TBitvector(0), h) } 
  $IsAlloc(v, TBitvector(0), h));

axiom (forall v: Set Box, t0: Ty :: 
  { $Is(v, TSet(t0)) } 
  $Is(v, TSet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: ISet Box, t0: Ty :: 
  { $Is(v, TISet(t0)) } 
  $Is(v, TISet(t0)) <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet Box, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0))
     <==> (forall bx: Box :: { v[bx] } 0 < v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: MultiSet Box, t0: Ty :: 
  { $Is(v, TMultiSet(t0)) } 
  $Is(v, TMultiSet(t0)) ==> $IsGoodMultiSet(v));

axiom (forall v: Seq Box, t0: Ty :: 
  { $Is(v, TSeq(t0)) } 
  $Is(v, TSeq(t0))
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsBox(Seq#Index(v, i), t0)));

axiom (forall v: Set Box, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSet(t0), h) } 
  $IsAlloc(v, TSet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: ISet Box, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TISet(t0), h) } 
  $IsAlloc(v, TISet(t0), h)
     <==> (forall bx: Box :: { v[bx] } v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: MultiSet Box, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TMultiSet(t0), h) } 
  $IsAlloc(v, TMultiSet(t0), h)
     <==> (forall bx: Box :: { v[bx] } 0 < v[bx] ==> $IsAllocBox(bx, t0, h)));

axiom (forall v: Seq Box, t0: Ty, h: Heap :: 
  { $IsAlloc(v, TSeq(t0), h) } 
  $IsAlloc(v, TSeq(t0), h)
     <==> (forall i: int :: 
      { Seq#Index(v, i) } 
      0 <= i && i < Seq#Length(v) ==> $IsAllocBox(Seq#Index(v, i), t0, h)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] } 
      Map#Domain(v)[bx] ==> $IsBox(Map#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TMap(t0, t1), h) } 
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] } 
      Map#Domain(v)[bx]
         ==> $IsAllocBox(Map#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty :: 
  { $Is(v, TMap(t0, t1)) } 
  $Is(v, TMap(t0, t1))
     ==> $Is(Map#Domain(v), TSet(t0))
       && $Is(Map#Values(v), TSet(t1))
       && $Is(Map#Items(v), TSet(Tclass._System.Tuple2(t0, t1))));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx] ==> $IsBox(IMap#Elements(v)[bx], t1) && $IsBox(bx, t0)));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty, h: Heap :: 
  { $IsAlloc(v, TIMap(t0, t1), h) } 
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box :: 
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] } 
      IMap#Domain(v)[bx]
         ==> $IsAllocBox(IMap#Elements(v)[bx], t1, h) && $IsAllocBox(bx, t0, h)));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty :: 
  { $Is(v, TIMap(t0, t1)) } 
  $Is(v, TIMap(t0, t1))
     ==> $Is(IMap#Domain(v), TISet(t0))
       && $Is(IMap#Values(v), TISet(t1))
       && $Is(IMap#Items(v), TISet(Tclass._System.Tuple2(t0, t1))));

const unique class._System.int: ClassName;

const unique class._System.bool: ClassName;

const unique class._System.set: ClassName;

const unique class._System.seq: ClassName;

const unique class._System.multiset: ClassName;

function Tclass._System.object?() : Ty;

function Tclass._System.Tuple2(Ty, Ty) : Ty;

function dtype(ref) : Ty;

function TypeTuple(a: ClassName, b: ClassName) : ClassName;

function TypeTupleCar(ClassName) : ClassName;

function TypeTupleCdr(ClassName) : ClassName;

axiom (forall a: ClassName, b: ClassName :: 
  { TypeTuple(a, b) } 
  TypeTupleCar(TypeTuple(a, b)) == a && TypeTupleCdr(TypeTuple(a, b)) == b);

function SetRef_to_SetBox(s: [ref]bool) : Set Box;

axiom (forall s: [ref]bool, bx: Box :: 
  { SetRef_to_SetBox(s)[bx] } 
  SetRef_to_SetBox(s)[bx] == s[$Unbox(bx): ref]);

axiom (forall s: [ref]bool :: 
  { SetRef_to_SetBox(s) } 
  $Is(SetRef_to_SetBox(s), TSet(Tclass._System.object?())));

function Apply1(Ty, Ty, Heap, HandleType, Box) : Box;

function DatatypeCtorId(DatatypeType) : DtCtorId;

function DtRank(DatatypeType) : int;

function BoxRank(Box) : int;

axiom (forall d: DatatypeType :: { BoxRank($Box(d)) } BoxRank($Box(d)) == DtRank(d));

type ORDINAL = Box;

function ORD#IsNat(ORDINAL) : bool;

function ORD#Offset(ORDINAL) : int;

axiom (forall o: ORDINAL :: { ORD#Offset(o) } 0 <= ORD#Offset(o));

function {:inline} ORD#IsLimit(o: ORDINAL) : bool
{
  ORD#Offset(o) == 0
}

function {:inline} ORD#IsSucc(o: ORDINAL) : bool
{
  0 < ORD#Offset(o)
}

function ORD#FromNat(int) : ORDINAL;

axiom (forall n: int :: 
  { ORD#FromNat(n) } 
  0 <= n ==> ORD#IsNat(ORD#FromNat(n)) && ORD#Offset(ORD#FromNat(n)) == n);

axiom (forall o: ORDINAL :: 
  { ORD#Offset(o) } { ORD#IsNat(o) } 
  ORD#IsNat(o) ==> o == ORD#FromNat(ORD#Offset(o)));

function ORD#Less(ORDINAL, ORDINAL) : bool;

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

function ORD#LessThanLimit(ORDINAL, ORDINAL) : bool;

axiom (forall o: ORDINAL, p: ORDINAL :: 
  { ORD#LessThanLimit(o, p) } 
  ORD#LessThanLimit(o, p) == ORD#Less(o, p));

function ORD#Plus(ORDINAL, ORDINAL) : ORDINAL;

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

function ORD#Minus(ORDINAL, ORDINAL) : ORDINAL;

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

const $ModuleContextHeight: int;

const $FunctionContextHeight: int;

const $LZ: LayerType;

function $LS(LayerType) : LayerType;

function AsFuelBottom(LayerType) : LayerType;

function AtLayer<A>([LayerType]A, LayerType) : A;

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, ly) } 
  AtLayer(f, ly) == f[ly]);

axiom (forall<A> f: [LayerType]A, ly: LayerType :: 
  { AtLayer(f, $LS(ly)) } 
  AtLayer(f, $LS(ly)) == AtLayer(f, ly));

function FDim<T>(Field T) : int;

function IndexField(int) : Field Box;

axiom (forall i: int :: { IndexField(i) } FDim(IndexField(i)) == 1);

function IndexField_Inverse<T>(Field T) : int;

axiom (forall i: int :: { IndexField(i) } IndexField_Inverse(IndexField(i)) == i);

function MultiIndexField(Field Box, int) : Field Box;

axiom (forall f: Field Box, i: int :: 
  { MultiIndexField(f, i) } 
  FDim(MultiIndexField(f, i)) == FDim(f) + 1);

function MultiIndexField_Inverse0<T>(Field T) : Field T;

function MultiIndexField_Inverse1<T>(Field T) : int;

axiom (forall f: Field Box, i: int :: 
  { MultiIndexField(f, i) } 
  MultiIndexField_Inverse0(MultiIndexField(f, i)) == f
     && MultiIndexField_Inverse1(MultiIndexField(f, i)) == i);

function DeclType<T>(Field T) : ClassName;

function DeclName<T>(Field T) : NameFamily;

function FieldOfDecl<alpha>(ClassName, NameFamily) : Field alpha;

axiom (forall<T> cl: ClassName, nm: NameFamily :: 
  { FieldOfDecl(cl, nm): Field T } 
  DeclType(FieldOfDecl(cl, nm): Field T) == cl
     && DeclName(FieldOfDecl(cl, nm): Field T) == nm);

function $IsGhostField<T>(Field T) : bool;

axiom (forall<T> h: Heap, k: Heap, v: T, t: Ty :: 
  { $HeapSucc(h, k), $IsAlloc(v, t, h) } 
  $HeapSucc(h, k) ==> $IsAlloc(v, t, h) ==> $IsAlloc(v, t, k));

axiom (forall h: Heap, k: Heap, bx: Box, t: Ty :: 
  { $HeapSucc(h, k), $IsAllocBox(bx, t, h) } 
  $HeapSucc(h, k) ==> $IsAllocBox(bx, t, h) ==> $IsAllocBox(bx, t, k));

const unique alloc: Field bool;

const unique allocName: NameFamily;

axiom FDim(alloc) == 0 && DeclName(alloc) == allocName && !$IsGhostField(alloc);

function _System.array.Length(a: ref) : int;

axiom (forall o: ref :: 0 <= _System.array.Length(o));

function Int(x: real) : int;

axiom (forall x: real :: { Int(x): int } Int(x): int == int(x));

function Real(x: int) : real;

axiom (forall x: int :: { Real(x): real } Real(x): real == real(x));

axiom (forall i: int :: { Int(Real(i)) } Int(Real(i)) == i);

function {:inline} _System.real.Floor(x: real) : int
{
  Int(x)
}

type Heap = [ref]<alpha>[Field alpha]alpha;

function {:inline} read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha
{
  H[r][f]
}

function {:inline} update<alpha>(H: Heap, r: ref, f: Field alpha, v: alpha) : Heap
{
  H[r := H[r][f := v]]
}

function $IsGoodHeap(Heap) : bool;

function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

const $OneHeap: Heap;

axiom $IsGoodHeap($OneHeap);

function $HeapSucc(Heap, Heap) : bool;

axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha :: 
  { update(h, r, f, x) } 
  $IsGoodHeap(update(h, r, f, x)) ==> $HeapSucc(h, update(h, r, f, x)));

axiom (forall a: Heap, b: Heap, c: Heap :: 
  { $HeapSucc(a, b), $HeapSucc(b, c) } 
  a != c ==> $HeapSucc(a, b) && $HeapSucc(b, c) ==> $HeapSucc(a, c));

axiom (forall h: Heap, k: Heap :: 
  { $HeapSucc(h, k) } 
  $HeapSucc(h, k)
     ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

function $HeapSuccGhost(Heap, Heap) : bool;

axiom (forall h: Heap, k: Heap :: 
  { $HeapSuccGhost(h, k) } 
  $HeapSuccGhost(h, k)
     ==> $HeapSucc(h, k)
       && (forall<alpha> o: ref, f: Field alpha :: 
        { read(k, o, f) } 
        !$IsGhostField(f) ==> read(h, o, f) == read(k, o, f)));

var $Tick: TickType;

procedure $YieldHavoc(this: ref, rds: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> 
      $o == this || rds[$Box($o)] || nw[$Box($o)]
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc0(this: ref, rds: Set Box, modi: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> 
      rds[$Box($o)] && !modi[$Box($o)] && $o != this
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterHavoc1(this: ref, modi: Set Box, nw: Set Box);
  modifies $Heap;
  ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || $o == this
         || modi[$Box($o)]
         || nw[$Box($o)]);
  ensures $HeapSucc(old($Heap), $Heap);



procedure $IterCollectNewObjects(prevHeap: Heap, newHeap: Heap, this: ref, NW: Field (Set Box))
   returns (s: Set Box);
  ensures (forall bx: Box :: 
    { s[bx] } 
    s[bx]
       <==> read(newHeap, this, NW)[bx]
         || (
          $Unbox(bx) != null
           && !read(prevHeap, $Unbox(bx): ref, alloc)
           && read(newHeap, $Unbox(bx): ref, alloc)));



type Set T = [T]bool;

function Set#Card<T>(Set T) : int;

axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

function Set#Empty<T>() : Set T;

axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);

axiom (forall<T> s: Set T :: 
  { Set#Card(s) } 
  (Set#Card(s) == 0 <==> s == Set#Empty())
     && (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

function Set#Singleton<T>(T) : Set T;

axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);

axiom (forall<T> r: T, o: T :: 
  { Set#Singleton(r)[o] } 
  Set#Singleton(r)[o] <==> r == o);

axiom (forall<T> r: T :: 
  { Set#Card(Set#Singleton(r)) } 
  Set#Card(Set#Singleton(r)) == 1);

function Set#UnionOne<T>(Set T, T) : Set T;

axiom (forall<T> a: Set T, x: T, o: T :: 
  { Set#UnionOne(a, x)[o] } 
  Set#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) } Set#UnionOne(a, x)[x]);

axiom (forall<T> a: Set T, x: T, y: T :: 
  { Set#UnionOne(a, x), a[y] } 
  a[y] ==> Set#UnionOne(a, x)[y]);

axiom (forall<T> a: Set T, x: T :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

axiom (forall<T> a: Set T, x: T :: 
  { Set#Card(Set#UnionOne(a, x)) } 
  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

function Set#Union<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T :: 
  { Set#Union(a, b)[o] } 
  Set#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall<T> a: Set T, b: Set T, y: T :: 
  { Set#Union(a, b), a[y] } 
  a[y] ==> Set#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T, y: T :: 
  { Set#Union(a, b), b[y] } 
  b[y] ==> Set#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Union(a, b) } 
  Set#Disjoint(a, b)
     ==> Set#Difference(Set#Union(a, b), a) == b
       && Set#Difference(Set#Union(a, b), b) == a);

function Set#Intersection<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T :: 
  { Set#Intersection(a, b)[o] } 
  Set#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Union(Set#Union(a, b), b) } 
  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Union(a, Set#Union(a, b)) } 
  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Intersection(Set#Intersection(a, b), b) } 
  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Intersection(a, Set#Intersection(a, b)) } 
  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Card(Set#Union(a, b)) } { Set#Card(Set#Intersection(a, b)) } 
  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
     == Set#Card(a) + Set#Card(b));

function Set#Difference<T>(Set T, Set T) : Set T;

axiom (forall<T> a: Set T, b: Set T, o: T :: 
  { Set#Difference(a, b)[o] } 
  Set#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall<T> a: Set T, b: Set T, y: T :: 
  { Set#Difference(a, b), b[y] } 
  b[y] ==> !Set#Difference(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Card(Set#Difference(a, b)) } 
  Set#Card(Set#Difference(a, b))
         + Set#Card(Set#Difference(b, a))
         + Set#Card(Set#Intersection(a, b))
       == Set#Card(Set#Union(a, b))
     && Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

function Set#Subset<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Subset(a, b) } 
  Set#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] ==> b[o]));

function Set#Equal<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Equal(a, b) } 
  Set#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall<T> a: Set T, b: Set T :: { Set#Equal(a, b) } Set#Equal(a, b) ==> a == b);

function Set#Disjoint<T>(Set T, Set T) : bool;

axiom (forall<T> a: Set T, b: Set T :: 
  { Set#Disjoint(a, b) } 
  Set#Disjoint(a, b) <==> (forall o: T :: { a[o] } { b[o] } !a[o] || !b[o]));

type ISet T = [T]bool;

function ISet#Empty<T>() : Set T;

axiom (forall<T> o: T :: { ISet#Empty()[o] } !ISet#Empty()[o]);

function ISet#UnionOne<T>(ISet T, T) : ISet T;

axiom (forall<T> a: ISet T, x: T, o: T :: 
  { ISet#UnionOne(a, x)[o] } 
  ISet#UnionOne(a, x)[o] <==> o == x || a[o]);

axiom (forall<T> a: ISet T, x: T :: { ISet#UnionOne(a, x) } ISet#UnionOne(a, x)[x]);

axiom (forall<T> a: ISet T, x: T, y: T :: 
  { ISet#UnionOne(a, x), a[y] } 
  a[y] ==> ISet#UnionOne(a, x)[y]);

function ISet#Union<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T :: 
  { ISet#Union(a, b)[o] } 
  ISet#Union(a, b)[o] <==> a[o] || b[o]);

axiom (forall<T> a: ISet T, b: ISet T, y: T :: 
  { ISet#Union(a, b), a[y] } 
  a[y] ==> ISet#Union(a, b)[y]);

axiom (forall<T> a: Set T, b: Set T, y: T :: 
  { ISet#Union(a, b), b[y] } 
  b[y] ==> ISet#Union(a, b)[y]);

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Union(a, b) } 
  ISet#Disjoint(a, b)
     ==> ISet#Difference(ISet#Union(a, b), a) == b
       && ISet#Difference(ISet#Union(a, b), b) == a);

function ISet#Intersection<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T :: 
  { ISet#Intersection(a, b)[o] } 
  ISet#Intersection(a, b)[o] <==> a[o] && b[o]);

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Union(ISet#Union(a, b), b) } 
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));

axiom (forall<T> a: Set T, b: Set T :: 
  { ISet#Union(a, ISet#Union(a, b)) } 
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Intersection(ISet#Intersection(a, b), b) } 
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Intersection(a, ISet#Intersection(a, b)) } 
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));

function ISet#Difference<T>(ISet T, ISet T) : ISet T;

axiom (forall<T> a: ISet T, b: ISet T, o: T :: 
  { ISet#Difference(a, b)[o] } 
  ISet#Difference(a, b)[o] <==> a[o] && !b[o]);

axiom (forall<T> a: ISet T, b: ISet T, y: T :: 
  { ISet#Difference(a, b), b[y] } 
  b[y] ==> !ISet#Difference(a, b)[y]);

function ISet#Subset<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Subset(a, b) } 
  ISet#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] ==> b[o]));

function ISet#Equal<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Equal(a, b) } 
  ISet#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <==> b[o]));

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Equal(a, b) } 
  ISet#Equal(a, b) ==> a == b);

function ISet#Disjoint<T>(ISet T, ISet T) : bool;

axiom (forall<T> a: ISet T, b: ISet T :: 
  { ISet#Disjoint(a, b) } 
  ISet#Disjoint(a, b) <==> (forall o: T :: { a[o] } { b[o] } !a[o] || !b[o]));

function Math#min(a: int, b: int) : int;

axiom (forall a: int, b: int :: { Math#min(a, b) } a <= b <==> Math#min(a, b) == a);

axiom (forall a: int, b: int :: { Math#min(a, b) } b <= a <==> Math#min(a, b) == b);

axiom (forall a: int, b: int :: 
  { Math#min(a, b) } 
  Math#min(a, b) == a || Math#min(a, b) == b);

function Math#clip(a: int) : int;

axiom (forall a: int :: { Math#clip(a) } 0 <= a ==> Math#clip(a) == a);

axiom (forall a: int :: { Math#clip(a) } a < 0 ==> Math#clip(a) == 0);

type MultiSet T = [T]int;

function $IsGoodMultiSet<T>(ms: MultiSet T) : bool;

axiom (forall<T> ms: MultiSet T :: 
  { $IsGoodMultiSet(ms) } 
  $IsGoodMultiSet(ms)
     <==> (forall bx: T :: { ms[bx] } 0 <= ms[bx] && ms[bx] <= MultiSet#Card(ms)));

function MultiSet#Card<T>(MultiSet T) : int;

axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));

axiom (forall<T> s: MultiSet T, x: T, n: int :: 
  { MultiSet#Card(s[x := n]) } 
  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);

function MultiSet#Empty<T>() : MultiSet T;

axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);

axiom (forall<T> s: MultiSet T :: 
  { MultiSet#Card(s) } 
  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty())
     && (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));

function MultiSet#Singleton<T>(T) : MultiSet T;

axiom (forall<T> r: T, o: T :: 
  { MultiSet#Singleton(r)[o] } 
  (MultiSet#Singleton(r)[o] == 1 <==> r == o)
     && (MultiSet#Singleton(r)[o] == 0 <==> r != o));

axiom (forall<T> r: T :: 
  { MultiSet#Singleton(r) } 
  MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));

function MultiSet#UnionOne<T>(MultiSet T, T) : MultiSet T;

axiom (forall<T> a: MultiSet T, x: T, o: T :: 
  { MultiSet#UnionOne(a, x)[o] } 
  0 < MultiSet#UnionOne(a, x)[o] <==> o == x || 0 < a[o]);

axiom (forall<T> a: MultiSet T, x: T :: 
  { MultiSet#UnionOne(a, x) } 
  MultiSet#UnionOne(a, x)[x] == a[x] + 1);

axiom (forall<T> a: MultiSet T, x: T, y: T :: 
  { MultiSet#UnionOne(a, x), a[y] } 
  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);

axiom (forall<T> a: MultiSet T, x: T, y: T :: 
  { MultiSet#UnionOne(a, x), a[y] } 
  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);

axiom (forall<T> a: MultiSet T, x: T :: 
  { MultiSet#Card(MultiSet#UnionOne(a, x)) } 
  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);

function MultiSet#Union<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: 
  { MultiSet#Union(a, b)[o] } 
  MultiSet#Union(a, b)[o] == a[o] + b[o]);

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Card(MultiSet#Union(a, b)) } 
  MultiSet#Card(MultiSet#Union(a, b)) == MultiSet#Card(a) + MultiSet#Card(b));

function MultiSet#Intersection<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: 
  { MultiSet#Intersection(a, b)[o] } 
  MultiSet#Intersection(a, b)[o] == Math#min(a[o], b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Intersection(MultiSet#Intersection(a, b), b) } 
  MultiSet#Intersection(MultiSet#Intersection(a, b), b)
     == MultiSet#Intersection(a, b));

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) } 
  MultiSet#Intersection(a, MultiSet#Intersection(a, b))
     == MultiSet#Intersection(a, b));

function MultiSet#Difference<T>(MultiSet T, MultiSet T) : MultiSet T;

axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: 
  { MultiSet#Difference(a, b)[o] } 
  MultiSet#Difference(a, b)[o] == Math#clip(a[o] - b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T, y: T :: 
  { MultiSet#Difference(a, b), b[y], a[y] } 
  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0);

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Card(MultiSet#Difference(a, b)) } 
  MultiSet#Card(MultiSet#Difference(a, b))
         + MultiSet#Card(MultiSet#Difference(b, a))
         + 2 * MultiSet#Card(MultiSet#Intersection(a, b))
       == MultiSet#Card(MultiSet#Union(a, b))
     && MultiSet#Card(MultiSet#Difference(a, b))
       == MultiSet#Card(a) - MultiSet#Card(MultiSet#Intersection(a, b)));

function MultiSet#Subset<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Subset(a, b) } 
  MultiSet#Subset(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] <= b[o]));

function MultiSet#Equal<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b) <==> (forall o: T :: { a[o] } { b[o] } a[o] == b[o]));

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Equal(a, b) } 
  MultiSet#Equal(a, b) ==> a == b);

function MultiSet#Disjoint<T>(MultiSet T, MultiSet T) : bool;

axiom (forall<T> a: MultiSet T, b: MultiSet T :: 
  { MultiSet#Disjoint(a, b) } 
  MultiSet#Disjoint(a, b)
     <==> (forall o: T :: { a[o] } { b[o] } a[o] == 0 || b[o] == 0));

function MultiSet#FromSet<T>(Set T) : MultiSet T;

axiom (forall<T> s: Set T, a: T :: 
  { MultiSet#FromSet(s)[a] } 
  (MultiSet#FromSet(s)[a] == 0 <==> !s[a])
     && (MultiSet#FromSet(s)[a] == 1 <==> s[a]));

axiom (forall<T> s: Set T :: 
  { MultiSet#Card(MultiSet#FromSet(s)) } 
  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));

function MultiSet#FromSeq<T>(Seq T) : MultiSet T;

axiom (forall<T> s: Seq T :: 
  { MultiSet#FromSeq(s) } 
  $IsGoodMultiSet(MultiSet#FromSeq(s)));

axiom (forall<T> s: Seq T :: 
  { MultiSet#Card(MultiSet#FromSeq(s)) } 
  MultiSet#Card(MultiSet#FromSeq(s)) == Seq#Length(s));

axiom (forall<T> s: Seq T, v: T :: 
  { MultiSet#FromSeq(Seq#Build(s, v)) } 
  MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v));

axiom (forall<T>  :: 
  MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);

axiom (forall<T> a: Seq T, b: Seq T :: 
  { MultiSet#FromSeq(Seq#Append(a, b)) } 
  MultiSet#FromSeq(Seq#Append(a, b))
     == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)));

axiom (forall<T> s: Seq T, i: int, v: T, x: T :: 
  { MultiSet#FromSeq(Seq#Update(s, i, v))[x] } 
  0 <= i && i < Seq#Length(s)
     ==> MultiSet#FromSeq(Seq#Update(s, i, v))[x]
       == MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s, i))), 
        MultiSet#Singleton(v))[x]);

axiom (forall<T> s: Seq T, x: T :: 
  { MultiSet#FromSeq(s)[x] } 
  (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && x == Seq#Index(s, i))
     <==> 0 < MultiSet#FromSeq(s)[x]);

function Seq#Length<T>(Seq T) : int;

axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

function Seq#Empty<T>() : Seq T;

axiom (forall<T>  :: { Seq#Empty(): Seq T } Seq#Length(Seq#Empty(): Seq T) == 0);

axiom (forall<T> s: Seq T :: 
  { Seq#Length(s) } 
  Seq#Length(s) == 0 ==> s == Seq#Empty());

function Seq#Singleton<T>(T) : Seq T;

axiom (forall<T> t: T :: 
  { Seq#Length(Seq#Singleton(t)) } 
  Seq#Length(Seq#Singleton(t)) == 1);

function Seq#Build<T>(s: Seq T, val: T) : Seq T;

function Seq#Build_inv0<T>(s: Seq T) : Seq T;

function Seq#Build_inv1<T>(s: Seq T) : T;

axiom (forall<T> s: Seq T, val: T :: 
  { Seq#Build(s, val) } 
  Seq#Build_inv0(Seq#Build(s, val)) == s
     && Seq#Build_inv1(Seq#Build(s, val)) == val);

axiom (forall<T> s: Seq T, v: T :: 
  { Seq#Build(s, v) } 
  Seq#Length(Seq#Build(s, v)) == 1 + Seq#Length(s));

axiom (forall<T> s: Seq T, i: int, v: T :: 
  { Seq#Index(Seq#Build(s, v), i) } 
  (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == v)
     && (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s, v), i) == Seq#Index(s, i)));

axiom (forall s: Seq Box, bx: Box, t: Ty :: 
  { $Is(Seq#Build(s, bx), TSeq(t)) } 
  $Is(s, TSeq(t)) && $IsBox(bx, t) ==> $Is(Seq#Build(s, bx), TSeq(t)));

function Seq#Create(ty: Ty, heap: Heap, len: int, init: HandleType) : Seq Box;

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType :: 
  { Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) } 
  $IsGoodHeap(heap) && 0 <= len
     ==> Seq#Length(Seq#Create(ty, heap, len, init): Seq Box) == len);

axiom (forall ty: Ty, heap: Heap, len: int, init: HandleType, i: int :: 
  { Seq#Index(Seq#Create(ty, heap, len, init), i) } 
  $IsGoodHeap(heap) && 0 <= i && i < len
     ==> Seq#Index(Seq#Create(ty, heap, len, init), i)
       == Apply1(TInt, TSeq(ty), heap, init, $Box(i)));

function Seq#Append<T>(Seq T, Seq T) : Seq T;

axiom (forall<T> s0: Seq T, s1: Seq T :: 
  { Seq#Length(Seq#Append(s0, s1)) } 
  Seq#Length(Seq#Append(s0, s1)) == Seq#Length(s0) + Seq#Length(s1));

function Seq#Index<T>(Seq T, int) : T;

axiom (forall<T> t: T :: 
  { Seq#Index(Seq#Singleton(t), 0) } 
  Seq#Index(Seq#Singleton(t), 0) == t);

axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: 
  { Seq#Index(Seq#Append(s0, s1), n) } 
  (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s0, n))
     && (Seq#Length(s0) <= n
       ==> Seq#Index(Seq#Append(s0, s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

function Seq#Update<T>(Seq T, int, T) : Seq T;

axiom (forall<T> s: Seq T, i: int, v: T :: 
  { Seq#Length(Seq#Update(s, i, v)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s, i, v)) == Seq#Length(s));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Index(Seq#Update(s, i, v), n) } 
  0 <= n && n < Seq#Length(s)
     ==> (i == n ==> Seq#Index(Seq#Update(s, i, v), n) == v)
       && (i != n ==> Seq#Index(Seq#Update(s, i, v), n) == Seq#Index(s, n)));

function Seq#Contains<T>(Seq T, T) : bool;

axiom (forall<T> s: Seq T, x: T :: 
  { Seq#Contains(s, x) } 
  Seq#Contains(s, x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall<T> x: T :: 
  { Seq#Contains(Seq#Empty(), x) } 
  !Seq#Contains(Seq#Empty(), x));

axiom (forall<T> s0: Seq T, s1: Seq T, x: T :: 
  { Seq#Contains(Seq#Append(s0, s1), x) } 
  Seq#Contains(Seq#Append(s0, s1), x)
     <==> Seq#Contains(s0, x) || Seq#Contains(s1, x));

axiom (forall<T> s: Seq T, v: T, x: T :: 
  { Seq#Contains(Seq#Build(s, v), x) } 
  Seq#Contains(Seq#Build(s, v), x) <==> v == x || Seq#Contains(s, x));

axiom (forall<T> s: Seq T, n: int, x: T :: 
  { Seq#Contains(Seq#Take(s, n), x) } 
  Seq#Contains(Seq#Take(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

axiom (forall<T> s: Seq T, n: int, x: T :: 
  { Seq#Contains(Seq#Drop(s, n), x) } 
  Seq#Contains(Seq#Drop(s, n), x)
     <==> (exists i: int :: 
      { Seq#Index(s, i) } 
      0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

function Seq#Equal<T>(Seq T, Seq T) : bool;

axiom (forall<T> s0: Seq T, s1: Seq T :: 
  { Seq#Equal(s0, s1) } 
  Seq#Equal(s0, s1)
     <==> Seq#Length(s0) == Seq#Length(s1)
       && (forall j: int :: 
        { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
        0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a, b) } Seq#Equal(a, b) ==> a == b);

function Seq#SameUntil<T>(Seq T, Seq T, int) : bool;

axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: 
  { Seq#SameUntil(s0, s1, n) } 
  Seq#SameUntil(s0, s1, n)
     <==> (forall j: int :: 
      { Seq#Index(s0, j) } { Seq#Index(s1, j) } 
      0 <= j && j < n ==> Seq#Index(s0, j) == Seq#Index(s1, j)));

function Seq#Take<T>(s: Seq T, howMany: int) : Seq T;

axiom (forall<T> s: Seq T, n: int :: 
  { Seq#Length(Seq#Take(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s, n)) == n);

axiom (forall<T> s: Seq T, n: int, j: int :: 
  {:weight 25} { Seq#Index(Seq#Take(s, n), j) } { Seq#Index(s, j), Seq#Take(s, n) } 
  0 <= j && j < n && j < Seq#Length(s)
     ==> Seq#Index(Seq#Take(s, n), j) == Seq#Index(s, j));

function Seq#Drop<T>(s: Seq T, howMany: int) : Seq T;

axiom (forall<T> s: Seq T, n: int :: 
  { Seq#Length(Seq#Drop(s, n)) } 
  0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s, n)) == Seq#Length(s) - n);

axiom (forall<T> s: Seq T, n: int, j: int :: 
  {:weight 25} { Seq#Index(Seq#Drop(s, n), j) } 
  0 <= n && 0 <= j && j < Seq#Length(s) - n
     ==> Seq#Index(Seq#Drop(s, n), j) == Seq#Index(s, j + n));

axiom (forall<T> s: Seq T, n: int, k: int :: 
  {:weight 25} { Seq#Index(s, k), Seq#Drop(s, n) } 
  0 <= n && n <= k && k < Seq#Length(s)
     ==> Seq#Index(Seq#Drop(s, n), k - n) == Seq#Index(s, k));

axiom (forall<T> s: Seq T, t: Seq T, n: int :: 
  { Seq#Take(Seq#Append(s, t), n) } { Seq#Drop(Seq#Append(s, t), n) } 
  n == Seq#Length(s)
     ==> Seq#Take(Seq#Append(s, t), n) == s && Seq#Drop(Seq#Append(s, t), n) == t);

function Seq#FromArray(h: Heap, a: ref) : Seq Box;

axiom (forall h: Heap, a: ref :: 
  { Seq#Length(Seq#FromArray(h, a)) } 
  Seq#Length(Seq#FromArray(h, a)) == _System.array.Length(a));

axiom (forall h: Heap, a: ref :: 
  { Seq#FromArray(h, a) } 
  (forall i: int :: 
    { read(h, a, IndexField(i)) } { Seq#Index(Seq#FromArray(h, a): Seq Box, i) } 
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

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n <= Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Take(Seq#Update(s, i, v), n) } 
  n <= i && i < Seq#Length(s)
     ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= n && n <= i && i < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i - n, v));

axiom (forall<T> s: Seq T, i: int, v: T, n: int :: 
  { Seq#Drop(Seq#Update(s, i, v), n) } 
  0 <= i && i < n && n < Seq#Length(s)
     ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

axiom (forall h: Heap, a: ref, n0: int, n1: int :: 
  { Seq#Take(Seq#FromArray(h, a), n0), Seq#Take(Seq#FromArray(h, a), n1) } 
  n0 + 1 == n1 && 0 <= n0 && n1 <= _System.array.Length(a)
     ==> Seq#Take(Seq#FromArray(h, a), n1)
       == Seq#Build(Seq#Take(Seq#FromArray(h, a), n0), read(h, a, IndexField(n0): Field Box)));

axiom (forall<T> s: Seq T, v: T, n: int :: 
  { Seq#Drop(Seq#Build(s, v), n) } 
  0 <= n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v));

function Seq#Rank<T>(Seq T) : int;

axiom (forall s: Seq Box, i: int :: 
  { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) } 
  0 <= i && i < Seq#Length(s)
     ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int :: 
  { Seq#Rank(Seq#Drop(s, i)) } 
  0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int :: 
  { Seq#Rank(Seq#Take(s, i)) } 
  0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s));

axiom (forall<T> s: Seq T, i: int, j: int :: 
  { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) } 
  0 <= i && i < j && j <= Seq#Length(s)
     ==> Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s));

axiom (forall<T> s: Seq T, n: int :: 
  { Seq#Drop(s, n) } 
  n == 0 ==> Seq#Drop(s, n) == s);

axiom (forall<T> s: Seq T, n: int :: 
  { Seq#Take(s, n) } 
  n == 0 ==> Seq#Take(s, n) == Seq#Empty());

axiom (forall<T> s: Seq T, m: int, n: int :: 
  { Seq#Drop(Seq#Drop(s, m), n) } 
  0 <= m && 0 <= n && m + n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m + n));

function Map#Domain<U,V>(Map U V) : Set U;

function Map#Elements<U,V>(Map U V) : [U]V;

function Map#Card<U,V>(Map U V) : int;

axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall<U,V> m: Map U V :: 
  { Map#Card(m) } 
  Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall<U,V> m: Map U V :: 
  { Map#Domain(m) } 
  m == Map#Empty() || (exists k: U :: Map#Domain(m)[k]));

axiom (forall<U,V> m: Map U V :: 
  { Map#Values(m) } 
  m == Map#Empty() || (exists v: V :: Map#Values(m)[v]));

axiom (forall<U,V> m: Map U V :: 
  { Map#Items(m) } 
  m == Map#Empty()
     || (exists k: Box, v: Box :: Map#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U,V> m: Map U V :: 
  { Set#Card(Map#Domain(m)) } 
  Set#Card(Map#Domain(m)) == Map#Card(m));

axiom (forall<U,V> m: Map U V :: 
  { Set#Card(Map#Values(m)) } 
  Set#Card(Map#Values(m)) <= Map#Card(m));

axiom (forall<U,V> m: Map U V :: 
  { Set#Card(Map#Items(m)) } 
  Set#Card(Map#Items(m)) == Map#Card(m));

function Map#Values<U,V>(Map U V) : Set V;

axiom (forall<U,V> m: Map U V, v: V :: 
  { Map#Values(m)[v] } 
  Map#Values(m)[v]
     == (exists u: U :: 
      { Map#Domain(m)[u] } { Map#Elements(m)[u] } 
      Map#Domain(m)[u] && v == Map#Elements(m)[u]));

function Map#Items<U,V>(Map U V) : Set Box;

function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;

function _System.Tuple2._0(DatatypeType) : Box;

function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map Box Box, item: Box :: 
  { Map#Items(m)[item] } 
  Map#Items(m)[item]
     <==> Map#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && Map#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

function Map#Empty<U,V>() : Map U V;

axiom (forall<U,V> u: U :: 
  { Map#Domain(Map#Empty(): Map U V)[u] } 
  !Map#Domain(Map#Empty(): Map U V)[u]);

function Map#Glue<U,V>([U]bool, [U]V, Ty) : Map U V;

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { Map#Domain(Map#Glue(a, b, t)) } 
  Map#Domain(Map#Glue(a, b, t)) == a);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { Map#Elements(Map#Glue(a, b, t)) } 
  Map#Elements(Map#Glue(a, b, t)) == b);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { $Is(Map#Glue(a, b, t), t) } 
  $Is(Map#Glue(a, b, t), t));

function Map#Build<U,V>(Map U V, U, V) : Map U V;

axiom (forall<U,V> m: Map U V, u: U, u': U, v: V :: 
  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] } 
  (u' == u
       ==> Map#Domain(Map#Build(m, u, v))[u'] && Map#Elements(Map#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u']
         && Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

axiom (forall<U,V> m: Map U V, u: U, v: V :: 
  { Map#Card(Map#Build(m, u, v)) } 
  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

axiom (forall<U,V> m: Map U V, u: U, v: V :: 
  { Map#Card(Map#Build(m, u, v)) } 
  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

function Map#Merge<U,V>(Map U V, Map U V) : Map U V;

axiom (forall<U,V> m: Map U V, n: Map U V :: 
  { Map#Domain(Map#Merge(m, n)) } 
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));

axiom (forall<U,V> m: Map U V, n: Map U V, u: U :: 
  { Map#Elements(Map#Merge(m, n))[u] } 
  Map#Domain(Map#Merge(m, n))[u]
     ==> (!Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u])
       && (Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

function Map#Subtract<U,V>(Map U V, Set U) : Map U V;

axiom (forall<U,V> m: Map U V, s: Set U :: 
  { Map#Domain(Map#Subtract(m, s)) } 
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));

axiom (forall<U,V> m: Map U V, s: Set U, u: U :: 
  { Map#Elements(Map#Subtract(m, s))[u] } 
  Map#Domain(Map#Subtract(m, s))[u]
     ==> Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

function Map#Equal<U,V>(Map U V, Map U V) : bool;

axiom (forall<U,V> m: Map U V, m': Map U V :: 
  { Map#Equal(m, m') } 
  Map#Equal(m, m')
     <==> (forall u: U :: Map#Domain(m)[u] == Map#Domain(m')[u])
       && (forall u: U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

axiom (forall<U,V> m: Map U V, m': Map U V :: 
  { Map#Equal(m, m') } 
  Map#Equal(m, m') ==> m == m');

function Map#Disjoint<U,V>(Map U V, Map U V) : bool;

axiom (forall<U,V> m: Map U V, m': Map U V :: 
  { Map#Disjoint(m, m') } 
  Map#Disjoint(m, m')
     <==> (forall o: U :: 
      { Map#Domain(m)[o] } { Map#Domain(m')[o] } 
      !Map#Domain(m)[o] || !Map#Domain(m')[o]));

function IMap#Domain<U,V>(IMap U V) : Set U;

function IMap#Elements<U,V>(IMap U V) : [U]V;

axiom (forall<U,V> m: IMap U V :: 
  { IMap#Domain(m) } 
  m == IMap#Empty() || (exists k: U :: IMap#Domain(m)[k]));

axiom (forall<U,V> m: IMap U V :: 
  { IMap#Values(m) } 
  m == IMap#Empty() || (exists v: V :: IMap#Values(m)[v]));

axiom (forall<U,V> m: IMap U V :: 
  { IMap#Items(m) } 
  m == IMap#Empty()
     || (exists k: Box, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U,V> m: IMap U V :: 
  { IMap#Domain(m) } 
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());

axiom (forall<U,V> m: IMap U V :: 
  { IMap#Values(m) } 
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());

axiom (forall<U,V> m: IMap U V :: 
  { IMap#Items(m) } 
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

function IMap#Values<U,V>(IMap U V) : Set V;

axiom (forall<U,V> m: IMap U V, v: V :: 
  { IMap#Values(m)[v] } 
  IMap#Values(m)[v]
     == (exists u: U :: 
      { IMap#Domain(m)[u] } { IMap#Elements(m)[u] } 
      IMap#Domain(m)[u] && v == IMap#Elements(m)[u]));

function IMap#Items<U,V>(IMap U V) : Set Box;

axiom (forall m: IMap Box Box, item: Box :: 
  { IMap#Items(m)[item] } 
  IMap#Items(m)[item]
     <==> IMap#Domain(m)[_System.Tuple2._0($Unbox(item))]
       && IMap#Elements(m)[_System.Tuple2._0($Unbox(item))]
         == _System.Tuple2._1($Unbox(item)));

function IMap#Empty<U,V>() : IMap U V;

axiom (forall<U,V> u: U :: 
  { IMap#Domain(IMap#Empty(): IMap U V)[u] } 
  !IMap#Domain(IMap#Empty(): IMap U V)[u]);

function IMap#Glue<U,V>([U]bool, [U]V, Ty) : IMap U V;

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { IMap#Domain(IMap#Glue(a, b, t)) } 
  IMap#Domain(IMap#Glue(a, b, t)) == a);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { IMap#Elements(IMap#Glue(a, b, t)) } 
  IMap#Elements(IMap#Glue(a, b, t)) == b);

axiom (forall<U,V> a: [U]bool, b: [U]V, t: Ty :: 
  { $Is(IMap#Glue(a, b, t), t) } 
  $Is(IMap#Glue(a, b, t), t));

function IMap#Build<U,V>(IMap U V, U, V) : IMap U V;

axiom (forall<U,V> m: IMap U V, u: U, u': U, v: V :: 
  { IMap#Domain(IMap#Build(m, u, v))[u'] } 
    { IMap#Elements(IMap#Build(m, u, v))[u'] } 
  (u' == u
       ==> IMap#Domain(IMap#Build(m, u, v))[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == v)
     && (u' != u
       ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u']
         && IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

function IMap#Equal<U,V>(IMap U V, IMap U V) : bool;

axiom (forall<U,V> m: IMap U V, m': IMap U V :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m')
     <==> (forall u: U :: IMap#Domain(m)[u] == IMap#Domain(m')[u])
       && (forall u: U :: 
        IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));

axiom (forall<U,V> m: IMap U V, m': IMap U V :: 
  { IMap#Equal(m, m') } 
  IMap#Equal(m, m') ==> m == m');

function IMap#Merge<U,V>(IMap U V, IMap U V) : IMap U V;

axiom (forall<U,V> m: IMap U V, n: IMap U V :: 
  { IMap#Domain(IMap#Merge(m, n)) } 
  IMap#Domain(IMap#Merge(m, n)) == Set#Union(IMap#Domain(m), IMap#Domain(n)));

axiom (forall<U,V> m: IMap U V, n: IMap U V, u: U :: 
  { IMap#Elements(IMap#Merge(m, n))[u] } 
  IMap#Domain(IMap#Merge(m, n))[u]
     ==> (!IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u])
       && (IMap#Domain(n)[u]
         ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

function IMap#Subtract<U,V>(IMap U V, Set U) : IMap U V;

axiom (forall<U,V> m: IMap U V, s: Set U :: 
  { IMap#Domain(IMap#Subtract(m, s)) } 
  IMap#Domain(IMap#Subtract(m, s)) == Set#Difference(IMap#Domain(m), s));

axiom (forall<U,V> m: IMap U V, s: Set U, u: U :: 
  { IMap#Elements(IMap#Subtract(m, s))[u] } 
  IMap#Domain(IMap#Subtract(m, s))[u]
     ==> IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);

function INTERNAL_add_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_add_boogie(x, y): int } 
  INTERNAL_add_boogie(x, y): int == x + y);

function INTERNAL_sub_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_sub_boogie(x, y): int } 
  INTERNAL_sub_boogie(x, y): int == x - y);

function INTERNAL_mul_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_mul_boogie(x, y): int } 
  INTERNAL_mul_boogie(x, y): int == x * y);

function INTERNAL_div_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_div_boogie(x, y): int } 
  INTERNAL_div_boogie(x, y): int == x div y);

function INTERNAL_mod_boogie(x: int, y: int) : int;

axiom (forall x: int, y: int :: 
  { INTERNAL_mod_boogie(x, y): int } 
  INTERNAL_mod_boogie(x, y): int == x mod y);

function {:never_pattern true} INTERNAL_lt_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_lt_boogie(x, y): bool } 
  INTERNAL_lt_boogie(x, y): bool == (x < y));

function {:never_pattern true} INTERNAL_le_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_le_boogie(x, y): bool } 
  INTERNAL_le_boogie(x, y): bool == (x <= y));

function {:never_pattern true} INTERNAL_gt_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_gt_boogie(x, y): bool } 
  INTERNAL_gt_boogie(x, y): bool == (x > y));

function {:never_pattern true} INTERNAL_ge_boogie(x: int, y: int) : bool;

axiom (forall x: int, y: int :: 
  {:never_pattern true} { INTERNAL_ge_boogie(x, y): bool } 
  INTERNAL_ge_boogie(x, y): bool == (x >= y));

function Mul(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Mul(x, y): int } Mul(x, y): int == x * y);

function Div(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Div(x, y): int } Div(x, y): int == x div y);

function Mod(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Mod(x, y): int } Mod(x, y): int == x mod y);

function Add(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Add(x, y): int } Add(x, y): int == x + y);

function Sub(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Sub(x, y): int } Sub(x, y): int == x - y);

function Tclass._System.nat() : Ty;

const unique Tagclass._System.nat: TyTag;

// Tclass._System.nat Tag
axiom Tag(Tclass._System.nat()) == Tagclass._System.nat
   && TagFamily(Tclass._System.nat()) == tytagFamily$nat;

// Box/unbox axiom for Tclass._System.nat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.nat()) } 
  $IsBox(bx, Tclass._System.nat())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._System.nat()));

// _System.nat: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._System.nat()) } 
  $Is(x#0, Tclass._System.nat()) <==> LitInt(0) <= x#0);

// _System.nat: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._System.nat(), $h) } 
  $IsAlloc(x#0, Tclass._System.nat(), $h));

const unique class._System.object?: ClassName;

const unique Tagclass._System.object?: TyTag;

// Tclass._System.object? Tag
axiom Tag(Tclass._System.object?()) == Tagclass._System.object?
   && TagFamily(Tclass._System.object?()) == tytagFamily$object;

// Box/unbox axiom for Tclass._System.object?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object?()) } 
  $IsBox(bx, Tclass._System.object?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object?()));

// object: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._System.object?()) } 
  $Is($o, Tclass._System.object?()));

// object: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.object?(), $h) } 
  $IsAlloc($o, Tclass._System.object?(), $h)
     <==> $o == null || read($h, $o, alloc));

function implements$_System.object(Ty) : bool;

function Tclass._System.object() : Ty;

const unique Tagclass._System.object: TyTag;

// Tclass._System.object Tag
axiom Tag(Tclass._System.object()) == Tagclass._System.object
   && TagFamily(Tclass._System.object()) == tytagFamily$object;

// Box/unbox axiom for Tclass._System.object
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.object()) } 
  $IsBox(bx, Tclass._System.object())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._System.object()));

// _System.object: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._System.object()) } 
  $Is(c#0, Tclass._System.object())
     <==> $Is(c#0, Tclass._System.object?()) && c#0 != null);

// _System.object: subset type $IsAlloc
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

// Tclass._System.array? injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array?(_System.array$arg) } 
  Tclass._System.array?_0(Tclass._System.array?(_System.array$arg))
     == _System.array$arg);

function Tclass._System.array?_0(Ty) : Ty;

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
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, IndexField($i0)), _System.array$arg, $h));

// array: Class $Is
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array?(_System.array$arg)) } 
  $Is($o, Tclass._System.array?(_System.array$arg))
     <==> $o == null || dtype($o) == Tclass._System.array?(_System.array$arg));

// array: Class $IsAlloc
axiom (forall _System.array$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h) } 
  $IsAlloc($o, Tclass._System.array?(_System.array$arg), $h)
     <==> $o == null || read($h, $o, alloc));

// array.Length: Type axiom
axiom (forall _System.array$arg: Ty, $o: ref :: 
  { _System.array.Length($o), Tclass._System.array?(_System.array$arg) } 
  $o != null && dtype($o) == Tclass._System.array?(_System.array$arg)
     ==> $Is(_System.array.Length($o), TInt));

// array.Length: Allocation axiom
axiom (forall _System.array$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array.Length($o), read($h, $o, alloc), Tclass._System.array?(_System.array$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array?(_System.array$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array.Length($o), TInt, $h));

function Tclass._System.array(Ty) : Ty;

const unique Tagclass._System.array: TyTag;

// Tclass._System.array Tag
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tag(Tclass._System.array(_System.array$arg)) == Tagclass._System.array
     && TagFamily(Tclass._System.array(_System.array$arg)) == tytagFamily$array);

// Tclass._System.array injectivity 0
axiom (forall _System.array$arg: Ty :: 
  { Tclass._System.array(_System.array$arg) } 
  Tclass._System.array_0(Tclass._System.array(_System.array$arg))
     == _System.array$arg);

function Tclass._System.array_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array
axiom (forall _System.array$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array(_System.array$arg)) } 
  $IsBox(bx, Tclass._System.array(_System.array$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array(_System.array$arg)));

// _System.array: subset type $Is
axiom (forall _System.array$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array(_System.array$arg)) } 
  $Is(c#0, Tclass._System.array(_System.array$arg))
     <==> $Is(c#0, Tclass._System.array?(_System.array$arg)) && c#0 != null);

// _System.array: subset type $IsAlloc
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

// Tclass._System.___hFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_0(Tclass._System.___hFunc1(#$T0, #$R)) == #$T0);

function Tclass._System.___hFunc1_0(Ty) : Ty;

// Tclass._System.___hFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc1(#$T0, #$R) } 
  Tclass._System.___hFunc1_1(Tclass._System.___hFunc1(#$T0, #$R)) == #$R);

function Tclass._System.___hFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc1(#$T0, #$R)));

function Handle1([Heap,Box]Box, [Heap,Box]bool, [Heap,Box]Set Box) : HandleType;

function Requires1(Ty, Ty, Heap, HandleType, Box) : bool;

function Reads1(Ty, Ty, Heap, HandleType, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set Box, 
    bx0: Box :: 
  { Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  Apply1(t0, t1, heap, Handle1(h, r, rd), bx0) == h[heap, bx0]);

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set Box, 
    bx0: Box :: 
  { Requires1(t0, t1, heap, Handle1(h, r, rd), bx0) } 
  r[heap, bx0] ==> Requires1(t0, t1, heap, Handle1(h, r, rd), bx0));

axiom (forall t0: Ty, 
    t1: Ty, 
    heap: Heap, 
    h: [Heap,Box]Box, 
    r: [Heap,Box]bool, 
    rd: [Heap,Box]Set Box, 
    bx0: Box, 
    bx: Box :: 
  { Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] } 
  Reads1(t0, t1, heap, Handle1(h, r, rd), bx0)[bx] == rd[heap, bx0][bx]);

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
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
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
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
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
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
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
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
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
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h0, f, bx0)[$Box(o)]
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
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads1(t0, t1, h1, f, bx0)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply1(t0, t1, h0, f, bx0) == Apply1(t0, t1, h1, f, bx0));

// empty-reads property for Reads1 
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Reads1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Reads1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap) && $IsBox(bx0, t0) && $Is(f, Tclass._System.___hFunc1(t0, t1))
     ==> (Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set Box)
       <==> Set#Equal(Reads1(t0, t1, heap, f, bx0), Set#Empty(): Set Box)));

// empty-reads property for Requires1
axiom (forall t0: Ty, t1: Ty, heap: Heap, f: HandleType, bx0: Box :: 
  { Requires1(t0, t1, $OneHeap, f, bx0), $IsGoodHeap(heap) } 
    { Requires1(t0, t1, heap, f, bx0) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $Is(f, Tclass._System.___hFunc1(t0, t1))
       && Set#Equal(Reads1(t0, t1, $OneHeap, f, bx0), Set#Empty(): Set Box)
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
            { Reads1(t0, t1, h, f, bx0)[$Box(r)] } 
            r != null && Reads1(t0, t1, h, f, bx0)[$Box(r)] ==> read(h, r, alloc)))));

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

// Tclass._System.___hPartialFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_0(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc1_0(Ty) : Ty;

// Tclass._System.___hPartialFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc1(#$T0, #$R) } 
  Tclass._System.___hPartialFunc1_1(Tclass._System.___hPartialFunc1(#$T0, #$R))
     == #$R);

function Tclass._System.___hPartialFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc1(#$T0, #$R)));

// _System._#PartialFunc1: subset type $Is
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc1(#$T0, #$R))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0)
           ==> Set#Equal(Reads1(#$T0, #$R, $OneHeap, f#0, x0#0), Set#Empty(): Set Box)));

// _System._#PartialFunc1: subset type $IsAlloc
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

// Tclass._System.___hTotalFunc1 injectivity 0
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_0(Tclass._System.___hTotalFunc1(#$T0, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc1_0(Ty) : Ty;

// Tclass._System.___hTotalFunc1 injectivity 1
axiom (forall #$T0: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc1(#$T0, #$R) } 
  Tclass._System.___hTotalFunc1_1(Tclass._System.___hTotalFunc1(#$T0, #$R)) == #$R);

function Tclass._System.___hTotalFunc1_1(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc1
axiom (forall #$T0: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc1(#$T0, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc1(#$T0, #$R)));

// _System._#TotalFunc1: subset type $Is
axiom (forall #$T0: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc1(#$T0, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc1(#$T0, #$R))
       && (forall x0#0: Box :: 
        $IsBox(x0#0, #$T0) ==> Requires1(#$T0, #$R, $OneHeap, f#0, x0#0)));

// _System._#TotalFunc1: subset type $IsAlloc
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

// Tclass._System.___hFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hFunc0(#$R) } 
  Tclass._System.___hFunc0_0(Tclass._System.___hFunc0(#$R)) == #$R);

function Tclass._System.___hFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc0(#$R)));

function Handle0([Heap]Box, [Heap]bool, [Heap]Set Box) : HandleType;

function Apply0(Ty, Heap, HandleType) : Box;

function Requires0(Ty, Heap, HandleType) : bool;

function Reads0(Ty, Heap, HandleType) : Set Box;

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box :: 
  { Apply0(t0, heap, Handle0(h, r, rd)) } 
  Apply0(t0, heap, Handle0(h, r, rd)) == h[heap]);

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box :: 
  { Requires0(t0, heap, Handle0(h, r, rd)) } 
  r[heap] ==> Requires0(t0, heap, Handle0(h, r, rd)));

axiom (forall t0: Ty, heap: Heap, h: [Heap]Box, r: [Heap]bool, rd: [Heap]Set Box, bx: Box :: 
  { Reads0(t0, heap, Handle0(h, r, rd))[bx] } 
  Reads0(t0, heap, Handle0(h, r, rd))[bx] == rd[heap][bx]);

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
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Reads0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Reads0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads0(t0, h0, f) == Reads0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Requires0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Requires0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires0(t0, h0, f) == Requires0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h0, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// frame axiom for Apply0
axiom (forall t0: Ty, h0: Heap, h1: Heap, f: HandleType :: 
  { $HeapSucc(h0, h1), Apply0(t0, h1, f) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads0(t0, h1, f)[$Box(o)] ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply0(t0, h0, f) == Apply0(t0, h1, f));

// empty-reads property for Reads0 
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Reads0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Reads0(t0, heap, f) } 
  $IsGoodHeap(heap) && $Is(f, Tclass._System.___hFunc0(t0))
     ==> (Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set Box)
       <==> Set#Equal(Reads0(t0, heap, f), Set#Empty(): Set Box)));

// empty-reads property for Requires0
axiom (forall t0: Ty, heap: Heap, f: HandleType :: 
  { Requires0(t0, $OneHeap, f), $IsGoodHeap(heap) } { Requires0(t0, heap, f) } 
  $IsGoodHeap(heap)
       && $Is(f, Tclass._System.___hFunc0(t0))
       && Set#Equal(Reads0(t0, $OneHeap, f), Set#Empty(): Set Box)
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
          { Reads0(t0, h, f)[$Box(r)] } 
          r != null && Reads0(t0, h, f)[$Box(r)] ==> read(h, r, alloc))));

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

// Tclass._System.___hPartialFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hPartialFunc0(#$R) } 
  Tclass._System.___hPartialFunc0_0(Tclass._System.___hPartialFunc0(#$R)) == #$R);

function Tclass._System.___hPartialFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc0(#$R)));

// _System._#PartialFunc0: subset type $Is
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hFunc0(#$R))
       && Set#Equal(Reads0(#$R, $OneHeap, f#0), Set#Empty(): Set Box));

// _System._#PartialFunc0: subset type $IsAlloc
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

// Tclass._System.___hTotalFunc0 injectivity 0
axiom (forall #$R: Ty :: 
  { Tclass._System.___hTotalFunc0(#$R) } 
  Tclass._System.___hTotalFunc0_0(Tclass._System.___hTotalFunc0(#$R)) == #$R);

function Tclass._System.___hTotalFunc0_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc0
axiom (forall #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc0(#$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc0(#$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc0(#$R)));

// _System._#TotalFunc0: subset type $Is
axiom (forall #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc0(#$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc0(#$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc0(#$R)) && Requires0(#$R, $OneHeap, f#0));

// _System._#TotalFunc0: subset type $IsAlloc
axiom (forall #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc0(#$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc0(#$R), $h));

const unique ##_System._tuple#2._#Make2: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: Box, a#0#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#0#0#0, a#0#1#0) } 
  DatatypeCtorId(#_System._tuple#2._#Make2(a#0#0#0, a#0#1#0))
     == ##_System._tuple#2._#Make2);

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

// Tclass._System.Tuple2 injectivity 0
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tclass._System.Tuple2_0(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T0);

function Tclass._System.Tuple2_0(Ty) : Ty;

// Tclass._System.Tuple2 injectivity 1
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty :: 
  { Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1) } 
  Tclass._System.Tuple2_1(Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     == _System._tuple#2$T1);

function Tclass._System.Tuple2_1(Ty) : Ty;

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
    a#3#0#0: Box, 
    a#3#1#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_System._tuple#2._#Make2(a#3#0#0, a#3#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#3#0#0, a#3#1#0), 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
        $h)
       <==> $IsAllocBox(a#3#0#0, _System._tuple#2$T0, $h)
         && $IsAllocBox(a#3#1#0, _System._tuple#2$T1, $h)));

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
axiom (forall a#4#0#0: Box, a#4#1#0: Box :: 
  { #_System._tuple#2._#Make2(Lit(a#4#0#0), Lit(a#4#1#0)) } 
  #_System._tuple#2._#Make2(Lit(a#4#0#0), Lit(a#4#1#0))
     == Lit(#_System._tuple#2._#Make2(a#4#0#0, a#4#1#0)));

// Constructor injectivity
axiom (forall a#5#0#0: Box, a#5#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#5#0#0, a#5#1#0) } 
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0)) == a#5#0#0);

// Inductive rank
axiom (forall a#6#0#0: Box, a#6#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0) } 
  BoxRank(a#6#0#0) < DtRank(#_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)));

// Constructor injectivity
axiom (forall a#7#0#0: Box, a#7#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#7#0#0, a#7#1#0) } 
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0)) == a#7#1#0);

// Inductive rank
axiom (forall a#8#0#0: Box, a#8#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#8#0#0, a#8#1#0) } 
  BoxRank(a#8#1#0) < DtRank(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0)));

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
  true
     ==> (_System.Tuple2#Equal(a, b)
       <==> _System.Tuple2._0(a) == _System.Tuple2._0(b)
         && _System.Tuple2._1(a) == _System.Tuple2._1(b)));

// Datatype extensionality axiom: _System._tuple#2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple2#Equal(a, b) } 
  _System.Tuple2#Equal(a, b) <==> a == b);

const unique class._System.Tuple2: ClassName;

// Constructor function declaration
function #_System._tuple#0._#Make0() : DatatypeType;

const unique ##_System._tuple#0._#Make0: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_System._tuple#0._#Make0()) == ##_System._tuple#0._#Make0;

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

function Tclass._System.Tuple0() : Ty;

const unique Tagclass._System.Tuple0: TyTag;

// Tclass._System.Tuple0 Tag
axiom Tag(Tclass._System.Tuple0()) == Tagclass._System.Tuple0
   && TagFamily(Tclass._System.Tuple0()) == tytagFamily$_tuple#0;

// Box/unbox axiom for Tclass._System.Tuple0
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._System.Tuple0()) } 
  $IsBox(bx, Tclass._System.Tuple0())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._System.Tuple0()));

// Constructor $Is
axiom $Is(#_System._tuple#0._#Make0(), Tclass._System.Tuple0());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_System._tuple#0._#Make0(), Tclass._System.Tuple0(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_System._tuple#0._#Make0(), Tclass._System.Tuple0(), $h));

// Constructor literal
axiom #_System._tuple#0._#Make0() == Lit(#_System._tuple#0._#Make0());

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
  true ==> (_System.Tuple0#Equal(a, b) <==> true));

// Datatype extensionality axiom: _System._tuple#0
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _System.Tuple0#Equal(a, b) } 
  _System.Tuple0#Equal(a, b) <==> a == b);

const unique class._System.Tuple0: ClassName;

const unique class._module.MyClass?: ClassName;

function Tclass._module.MyClass?(Ty) : Ty;

const unique Tagclass._module.MyClass?: TyTag;

// Tclass._module.MyClass? Tag
axiom (forall _module.MyClass$G: Ty :: 
  { Tclass._module.MyClass?(_module.MyClass$G) } 
  Tag(Tclass._module.MyClass?(_module.MyClass$G)) == Tagclass._module.MyClass?
     && TagFamily(Tclass._module.MyClass?(_module.MyClass$G)) == tytagFamily$MyClass);

// Tclass._module.MyClass? injectivity 0
axiom (forall _module.MyClass$G: Ty :: 
  { Tclass._module.MyClass?(_module.MyClass$G) } 
  Tclass._module.MyClass?_0(Tclass._module.MyClass?(_module.MyClass$G))
     == _module.MyClass$G);

function Tclass._module.MyClass?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.MyClass?
axiom (forall _module.MyClass$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.MyClass?(_module.MyClass$G)) } 
  $IsBox(bx, Tclass._module.MyClass?(_module.MyClass$G))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyClass?(_module.MyClass$G)));

// MyClass: Class $Is
axiom (forall _module.MyClass$G: Ty, $o: ref :: 
  { $Is($o, Tclass._module.MyClass?(_module.MyClass$G)) } 
  $Is($o, Tclass._module.MyClass?(_module.MyClass$G))
     <==> $o == null || dtype($o) == Tclass._module.MyClass?(_module.MyClass$G));

// MyClass: Class $IsAlloc
axiom (forall _module.MyClass$G: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.MyClass?(_module.MyClass$G), $h) } 
  $IsAlloc($o, Tclass._module.MyClass?(_module.MyClass$G), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.MyClass.x(_module.MyClass$G: Ty, this: ref) : Box;

// MyClass.x: Type axiom
axiom 7 < $FunctionContextHeight
   ==> (forall _module.MyClass$G: Ty, $o: ref :: 
    { _module.MyClass.x(_module.MyClass$G, $o) } 
    $IsBox(_module.MyClass.x(_module.MyClass$G, $o), _module.MyClass$G));

// MyClass.x: Allocation axiom
axiom 7 < $FunctionContextHeight
   ==> (forall _module.MyClass$G: Ty, $h: Heap, $o: ref :: 
    { _module.MyClass.x(_module.MyClass$G, $o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAllocBox(_module.MyClass.x(_module.MyClass$G, $o), _module.MyClass$G, $h));

axiom FDim(_module.MyClass.y) == 0
   && FieldOfDecl(class._module.MyClass?, field$y) == _module.MyClass.y
   && !$IsGhostField(_module.MyClass.y);

const _module.MyClass.y: Field Box;

// MyClass.y: Type axiom
axiom (forall _module.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.y), Tclass._module.MyClass?(_module.MyClass$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?(_module.MyClass$G)
     ==> $IsBox(read($h, $o, _module.MyClass.y), _module.MyClass$G));

// MyClass.y: Allocation axiom
axiom (forall _module.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.y), Tclass._module.MyClass?(_module.MyClass$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?(_module.MyClass$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.MyClass.y), _module.MyClass$G, $h));

axiom FDim(_module.MyClass.oxA) == 0
   && FieldOfDecl(class._module.MyClass?, field$oxA) == _module.MyClass.oxA
   && $IsGhostField(_module.MyClass.oxA);

const _module.MyClass.oxA: Field Box;

// MyClass.oxA: Type axiom
axiom (forall _module.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.oxA), Tclass._module.MyClass?(_module.MyClass$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?(_module.MyClass$G)
     ==> $IsBox(read($h, $o, _module.MyClass.oxA), _module.MyClass$G));

// MyClass.oxA: Allocation axiom
axiom (forall _module.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.oxA), Tclass._module.MyClass?(_module.MyClass$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?(_module.MyClass$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.MyClass.oxA), _module.MyClass$G, $h));

function _module.MyClass.oxB(_module.MyClass$G: Ty, this: ref) : Box;

// MyClass.oxB: Type axiom
axiom 38 < $FunctionContextHeight
   ==> (forall _module.MyClass$G: Ty, $o: ref :: 
    { _module.MyClass.oxB(_module.MyClass$G, $o) } 
    $IsBox(_module.MyClass.oxB(_module.MyClass$G, $o), _module.MyClass$G));

// MyClass.oxB: Allocation axiom
axiom 38 < $FunctionContextHeight
   ==> (forall _module.MyClass$G: Ty, $h: Heap, $o: ref :: 
    { _module.MyClass.oxB(_module.MyClass$G, $o), read($h, $o, alloc) } 
    $IsGoodHeap($h) && read($h, $o, alloc)
       ==> $IsAllocBox(_module.MyClass.oxB(_module.MyClass$G, $o), _module.MyClass$G, $h));

function Tclass._module.MyClass(Ty) : Ty;

const unique Tagclass._module.MyClass: TyTag;

// Tclass._module.MyClass Tag
axiom (forall _module.MyClass$G: Ty :: 
  { Tclass._module.MyClass(_module.MyClass$G) } 
  Tag(Tclass._module.MyClass(_module.MyClass$G)) == Tagclass._module.MyClass
     && TagFamily(Tclass._module.MyClass(_module.MyClass$G)) == tytagFamily$MyClass);

// Tclass._module.MyClass injectivity 0
axiom (forall _module.MyClass$G: Ty :: 
  { Tclass._module.MyClass(_module.MyClass$G) } 
  Tclass._module.MyClass_0(Tclass._module.MyClass(_module.MyClass$G))
     == _module.MyClass$G);

function Tclass._module.MyClass_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.MyClass
axiom (forall _module.MyClass$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.MyClass(_module.MyClass$G)) } 
  $IsBox(bx, Tclass._module.MyClass(_module.MyClass$G))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyClass(_module.MyClass$G)));

procedure CheckWellformed$$_module.MyClass.C0(_module.MyClass$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass(_module.MyClass$G))
         && $IsAlloc(this, Tclass._module.MyClass(_module.MyClass$G), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyClass.C0(_module.MyClass$G: Ty)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass(_module.MyClass$G))
         && $IsAlloc(this, Tclass._module.MyClass(_module.MyClass$G), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.MyClass.C0(_module.MyClass$G: Ty)
   returns (this: ref
       where this != null && $Is(this, Tclass._module.MyClass(_module.MyClass$G)), 
    $_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.MyClass.C0(_module.MyClass$G: Ty) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.x: Box;
  var this.y: Box;
  var this.oxA: Box;
  var this.oxB: Box;
  var defass#this.x: bool;
  var defass#this.y: bool;
  var defass#this.oxA: bool;
  var defass#this.oxB: bool;

    // AddMethodImpl: C0, Impl$$_module.MyClass.C0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(10,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(10,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(11,7)
    assume true;
    assert defass#this.y;
    assume true;
    this.x := this.y;
    defass#this.x := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(11,10)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(12,12)
    assume true;
    assert defass#this.x;
    assume true;
    this.y := this.x;
    defass#this.y := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(12,26)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(10,3)
    assert defass#this.x;
    assert defass#this.y;
    assert defass#this.oxA;
    assert defass#this.oxB;
    assume !read($Heap, this, alloc);
    assume _module.MyClass.x(_module.MyClass$G, this) == this.x;
    assume read($Heap, this, _module.MyClass.y) == this.y;
    assume read($Heap, this, _module.MyClass.oxA) == this.oxA;
    assume _module.MyClass.oxB(_module.MyClass$G, this) == this.oxB;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(10,3)
}



procedure CheckWellformed$$_module.MyClass.C1(_module.MyClass$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass(_module.MyClass$G))
         && $IsAlloc(this, Tclass._module.MyClass(_module.MyClass$G), $Heap), 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyClass.C1(_module.MyClass$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass(_module.MyClass$G))
         && $IsAlloc(this, Tclass._module.MyClass(_module.MyClass$G), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.MyClass.C1(_module.MyClass$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap))
   returns (this: ref
       where this != null && $Is(this, Tclass._module.MyClass(_module.MyClass$G)), 
    $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.MyClass.C1(_module.MyClass$G: Ty, g#0: Box) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.x: Box;
  var this.y: Box;
  var this.oxA: Box;
  var this.oxB: Box;
  var defass#this.x: bool;
  var defass#this.y: bool;
  var defass#this.oxA: bool;
  var defass#this.oxB: bool;

    // AddMethodImpl: C1, Impl$$_module.MyClass.C1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(16,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(16,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(17,7)
    assume true;
    assume true;
    this.x := g#0;
    defass#this.x := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(17,10)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(16,3)
    assert defass#this.x;
    assert defass#this.y;
    assert defass#this.oxA;
    assert defass#this.oxB;
    assume !read($Heap, this, alloc);
    assume _module.MyClass.x(_module.MyClass$G, this) == this.x;
    assume read($Heap, this, _module.MyClass.y) == this.y;
    assume read($Heap, this, _module.MyClass.oxA) == this.oxA;
    assume _module.MyClass.oxB(_module.MyClass$G, this) == this.oxB;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(16,3)
}



procedure CheckWellformed$$_module.MyClass.C2(_module.MyClass$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass(_module.MyClass$G))
         && $IsAlloc(this, Tclass._module.MyClass(_module.MyClass$G), $Heap), 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyClass.C2(_module.MyClass$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass(_module.MyClass$G))
         && $IsAlloc(this, Tclass._module.MyClass(_module.MyClass$G), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.MyClass.C2(_module.MyClass$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap))
   returns (this: ref
       where this != null && $Is(this, Tclass._module.MyClass(_module.MyClass$G)), 
    $_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.MyClass.C2(_module.MyClass$G: Ty, g#0: Box) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.x: Box;
  var this.y: Box;
  var this.oxA: Box;
  var this.oxB: Box;
  var defass#this.x: bool;
  var defass#this.y: bool;
  var defass#this.oxA: bool;
  var defass#this.oxB: bool;

    // AddMethodImpl: C2, Impl$$_module.MyClass.C2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(21,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(21,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(22,7)
    assume true;
    assume true;
    this.x := g#0;
    defass#this.x := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(22,10)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(21,3)
    assert defass#this.x;
    assert defass#this.y;
    assert defass#this.oxA;
    assert defass#this.oxB;
    assume !read($Heap, this, alloc);
    assume _module.MyClass.x(_module.MyClass$G, this) == this.x;
    assume read($Heap, this, _module.MyClass.y) == this.y;
    assume read($Heap, this, _module.MyClass.oxA) == this.oxA;
    assume _module.MyClass.oxB(_module.MyClass$G, this) == this.oxB;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(21,3)
}



procedure CheckWellformed$$_module.MyClass.C3(_module.MyClass$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass(_module.MyClass$G))
         && $IsAlloc(this, Tclass._module.MyClass(_module.MyClass$G), $Heap), 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyClass.C3(_module.MyClass$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClass(_module.MyClass$G))
         && $IsAlloc(this, Tclass._module.MyClass(_module.MyClass$G), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.MyClass.C3(_module.MyClass$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module.MyClass$G) && $IsAllocBox(g#0, _module.MyClass$G, $Heap))
   returns (this: ref
       where this != null && $Is(this, Tclass._module.MyClass(_module.MyClass$G)), 
    $_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.MyClass.C3(_module.MyClass$G: Ty, g#0: Box) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.x: Box;
  var this.y: Box;
  var this.oxA: Box;
  var this.oxB: Box;
  var defass#this.x: bool;
  var defass#this.y: bool;
  var defass#this.oxA: bool;
  var defass#this.oxB: bool;

    // AddMethodImpl: C3, Impl$$_module.MyClass.C3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(25,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(25,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(26,7)
    assume true;
    assume true;
    this.y := g#0;
    defass#this.y := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(26,10)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(25,3)
    assert defass#this.x;
    assert defass#this.y;
    assert defass#this.oxA;
    assert defass#this.oxB;
    assume !read($Heap, this, alloc);
    assume _module.MyClass.x(_module.MyClass$G, this) == this.x;
    assume read($Heap, this, _module.MyClass.y) == this.y;
    assume read($Heap, this, _module.MyClass.oxA) == this.oxA;
    assume _module.MyClass.oxB(_module.MyClass$G, this) == this.oxB;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(25,3)
}



// _module.MyClass: subset type $Is
axiom (forall _module.MyClass$G: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.MyClass(_module.MyClass$G)) } 
  $Is(c#0, Tclass._module.MyClass(_module.MyClass$G))
     <==> $Is(c#0, Tclass._module.MyClass?(_module.MyClass$G)) && c#0 != null);

// _module.MyClass: subset type $IsAlloc
axiom (forall _module.MyClass$G: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.MyClass(_module.MyClass$G), $h) } 
  $IsAlloc(c#0, Tclass._module.MyClass(_module.MyClass$G), $h)
     <==> $IsAlloc(c#0, Tclass._module.MyClass?(_module.MyClass$G), $h));

const unique class._module.C?: ClassName;

function Tclass._module.C?() : Ty;

const unique Tagclass._module.C?: TyTag;

// Tclass._module.C? Tag
axiom Tag(Tclass._module.C?()) == Tagclass._module.C?
   && TagFamily(Tclass._module.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass._module.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.C?()) } 
  $IsBox(bx, Tclass._module.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.C?()) } 
  $Is($o, Tclass._module.C?()) <==> $o == null || dtype($o) == Tclass._module.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.C?(), $h) } 
  $IsAlloc($o, Tclass._module.C?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.C.u) == 0
   && FieldOfDecl(class._module.C?, field$u) == _module.C.u
   && !$IsGhostField(_module.C.u);

const _module.C.u: Field int;

// C.u: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.u) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.C?()
     ==> $Is(read($h, $o, _module.C.u), TInt));

// C.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.u) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.C.u), TInt, $h));

function Tclass._module.C() : Ty;

const unique Tagclass._module.C: TyTag;

// Tclass._module.C Tag
axiom Tag(Tclass._module.C()) == Tagclass._module.C
   && TagFamily(Tclass._module.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass._module.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.C()) } 
  $IsBox(bx, Tclass._module.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.C()));

// _module.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.C()) } 
  $Is(c#0, Tclass._module.C()) <==> $Is(c#0, Tclass._module.C?()) && c#0 != null);

// _module.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.C(), $h) } 
  $IsAlloc(c#0, Tclass._module.C(), $h)
     <==> $IsAlloc(c#0, Tclass._module.C?(), $h));

procedure CheckWellformed$$_module.NonNullC(c#0: ref where $Is(c#0, Tclass._module.C?()));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NonNullC(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type NonNullC
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(69,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume c#0 != null;
    }
    else
    {
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.F#canCall();
        assume _module.__default.F#canCall();
        assert _module.__default.F() != null;
    }
}



function Tclass._module.NonNullC() : Ty;

const unique Tagclass._module.NonNullC: TyTag;

// Tclass._module.NonNullC Tag
axiom Tag(Tclass._module.NonNullC()) == Tagclass._module.NonNullC
   && TagFamily(Tclass._module.NonNullC()) == tytagFamily$NonNullC;

// Box/unbox axiom for Tclass._module.NonNullC
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NonNullC()) } 
  $IsBox(bx, Tclass._module.NonNullC())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.NonNullC()));

// _module.NonNullC: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.NonNullC()) } 
  $Is(c#0, Tclass._module.NonNullC())
     <==> $Is(c#0, Tclass._module.C?()) && c#0 != null);

// _module.NonNullC: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.NonNullC(), $h) } 
  $IsAlloc(c#0, Tclass._module.NonNullC(), $h)
     <==> $IsAlloc(c#0, Tclass._module.C?(), $h));

const unique class._module.Iter?: ClassName;

function Tclass._module.Iter?(Ty) : Ty;

const unique Tagclass._module.Iter?: TyTag;

// Tclass._module.Iter? Tag
axiom (forall _module.Iter$G: Ty :: 
  { Tclass._module.Iter?(_module.Iter$G) } 
  Tag(Tclass._module.Iter?(_module.Iter$G)) == Tagclass._module.Iter?
     && TagFamily(Tclass._module.Iter?(_module.Iter$G)) == tytagFamily$Iter);

// Tclass._module.Iter? injectivity 0
axiom (forall _module.Iter$G: Ty :: 
  { Tclass._module.Iter?(_module.Iter$G) } 
  Tclass._module.Iter?_0(Tclass._module.Iter?(_module.Iter$G)) == _module.Iter$G);

function Tclass._module.Iter?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Iter?
axiom (forall _module.Iter$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Iter?(_module.Iter$G)) } 
  $IsBox(bx, Tclass._module.Iter?(_module.Iter$G))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Iter?(_module.Iter$G)));

// Iter: Class $Is
axiom (forall _module.Iter$G: Ty, $o: ref :: 
  { $Is($o, Tclass._module.Iter?(_module.Iter$G)) } 
  $Is($o, Tclass._module.Iter?(_module.Iter$G))
     <==> $o == null || dtype($o) == Tclass._module.Iter?(_module.Iter$G));

// Iter: Class $IsAlloc
axiom (forall _module.Iter$G: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Iter?(_module.Iter$G), $h) } 
  $IsAlloc($o, Tclass._module.Iter?(_module.Iter$G), $h)
     <==> $o == null || read($h, $o, alloc));

function _module.Iter.n(ref) : int;

// Iter.n: Type axiom
axiom (forall _module.Iter$G: Ty, $o: ref :: 
  { _module.Iter.n($o), Tclass._module.Iter?(_module.Iter$G) } 
  $o != null && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $Is(_module.Iter.n($o), Tclass._System.nat()));

// Iter.n: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { _module.Iter.n($o), read($h, $o, alloc), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter.n($o), Tclass._System.nat(), $h));

function _module.Iter.g(ref) : Box;

// Iter.g: Type axiom
axiom (forall _module.Iter$G: Ty, $o: ref :: 
  { _module.Iter.g($o), Tclass._module.Iter?(_module.Iter$G) } 
  $o != null && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $IsBox(_module.Iter.g($o), _module.Iter$G));

// Iter.g: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { _module.Iter.g($o), read($h, $o, alloc), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(_module.Iter.g($o), _module.Iter$G, $h));

axiom FDim(_module.Iter.y) == 0
   && FieldOfDecl(class._module.Iter?, field$y) == _module.Iter.y
   && !$IsGhostField(_module.Iter.y);

const _module.Iter.y: Field Box;

// Iter.y: Type axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.y), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $IsBox(read($h, $o, _module.Iter.y), _module.Iter$G));

// Iter.y: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.y), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.Iter.y), _module.Iter$G, $h));

axiom FDim(_module.Iter.ug) == 0
   && FieldOfDecl(class._module.Iter?, field$ug) == _module.Iter.ug
   && $IsGhostField(_module.Iter.ug);

const _module.Iter.ug: Field Box;

// Iter.ug: Type axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.ug), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $IsBox(read($h, $o, _module.Iter.ug), _module.Iter$G));

// Iter.ug: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.ug), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.Iter.ug), _module.Iter$G, $h));

axiom FDim(_module.Iter.z) == 0
   && FieldOfDecl(class._module.Iter?, field$z) == _module.Iter.z
   && !$IsGhostField(_module.Iter.z);

const _module.Iter.z: Field Box;

// Iter.z: Type axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.z), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $IsBox(read($h, $o, _module.Iter.z), _module.Iter$G));

// Iter.z: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.z), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.Iter.z), _module.Iter$G, $h));

axiom FDim(_module.Iter.ys) == 0
   && FieldOfDecl(class._module.Iter?, field$ys) == _module.Iter.ys
   && $IsGhostField(_module.Iter.ys);

const _module.Iter.ys: Field (Seq Box);

// Iter.ys: Type axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.ys), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $Is(read($h, $o, _module.Iter.ys), TSeq(_module.Iter$G)));

// Iter.ys: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.ys), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Iter.ys), TSeq(_module.Iter$G), $h));

axiom FDim(_module.Iter.ugs) == 0
   && FieldOfDecl(class._module.Iter?, field$ugs) == _module.Iter.ugs
   && $IsGhostField(_module.Iter.ugs);

const _module.Iter.ugs: Field (Seq Box);

// Iter.ugs: Type axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.ugs), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $Is(read($h, $o, _module.Iter.ugs), TSeq(_module.Iter$G)));

// Iter.ugs: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.ugs), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Iter.ugs), TSeq(_module.Iter$G), $h));

axiom FDim(_module.Iter.zs) == 0
   && FieldOfDecl(class._module.Iter?, field$zs) == _module.Iter.zs
   && $IsGhostField(_module.Iter.zs);

const _module.Iter.zs: Field (Seq Box);

// Iter.zs: Type axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.zs), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $Is(read($h, $o, _module.Iter.zs), TSeq(_module.Iter$G)));

// Iter.zs: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.zs), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Iter.zs), TSeq(_module.Iter$G), $h));

function _module.Iter.__reads(ref) : Set Box;

// Iter._reads: Type axiom
axiom (forall _module.Iter$G: Ty, $o: ref :: 
  { _module.Iter.__reads($o), Tclass._module.Iter?(_module.Iter$G) } 
  $o != null && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $Is(_module.Iter.__reads($o), TSet(Tclass._System.object?())));

// Iter._reads: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { _module.Iter.__reads($o), read($h, $o, alloc), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.Iter.__modifies(ref) : Set Box;

// Iter._modifies: Type axiom
axiom (forall _module.Iter$G: Ty, $o: ref :: 
  { _module.Iter.__modifies($o), Tclass._module.Iter?(_module.Iter$G) } 
  $o != null && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $Is(_module.Iter.__modifies($o), TSet(Tclass._System.object?())));

// Iter._modifies: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { _module.Iter.__modifies($o), read($h, $o, alloc), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.Iter.__new) == 0
   && FieldOfDecl(class._module.Iter?, field$_new) == _module.Iter.__new
   && $IsGhostField(_module.Iter.__new);

const _module.Iter.__new: Field (Set Box);

// Iter._new: Type axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.__new), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $Is(read($h, $o, _module.Iter.__new), TSet(Tclass._System.object?())));

// Iter._new: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter.__new), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Iter.__new), TSet(Tclass._System.object?()), $h));

function _module.Iter.__decreases0(ref) : int;

// Iter._decreases0: Type axiom
axiom (forall _module.Iter$G: Ty, $o: ref :: 
  { _module.Iter.__decreases0($o), Tclass._module.Iter?(_module.Iter$G) } 
  $o != null && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $Is(_module.Iter.__decreases0($o), TInt));

// Iter._decreases0: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { _module.Iter.__decreases0($o), read($h, $o, alloc), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter.__decreases0($o), TInt, $h));

function _module.Iter.__decreases1(ref) : Box;

// Iter._decreases1: Type axiom
axiom (forall _module.Iter$G: Ty, $o: ref :: 
  { _module.Iter.__decreases1($o), Tclass._module.Iter?(_module.Iter$G) } 
  $o != null && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
     ==> $IsBox(_module.Iter.__decreases1($o), _module.Iter$G));

// Iter._decreases1: Allocation axiom
axiom (forall _module.Iter$G: Ty, $h: Heap, $o: ref :: 
  { _module.Iter.__decreases1($o), read($h, $o, alloc), Tclass._module.Iter?(_module.Iter$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter?(_module.Iter$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(_module.Iter.__decreases1($o), _module.Iter$G, $h));

function Tclass._module.Iter(Ty) : Ty;

const unique Tagclass._module.Iter: TyTag;

// Tclass._module.Iter Tag
axiom (forall _module.Iter$G: Ty :: 
  { Tclass._module.Iter(_module.Iter$G) } 
  Tag(Tclass._module.Iter(_module.Iter$G)) == Tagclass._module.Iter
     && TagFamily(Tclass._module.Iter(_module.Iter$G)) == tytagFamily$Iter);

// Tclass._module.Iter injectivity 0
axiom (forall _module.Iter$G: Ty :: 
  { Tclass._module.Iter(_module.Iter$G) } 
  Tclass._module.Iter_0(Tclass._module.Iter(_module.Iter$G)) == _module.Iter$G);

function Tclass._module.Iter_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Iter
axiom (forall _module.Iter$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Iter(_module.Iter$G)) } 
  $IsBox(bx, Tclass._module.Iter(_module.Iter$G))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Iter(_module.Iter$G)));

procedure CheckWellformed$$_module.Iter.__ctor(_module.Iter$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter(_module.Iter$G))
         && $IsAlloc(this, Tclass._module.Iter(_module.Iter$G), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    g#0: Box
       where $IsBox(g#0, _module.Iter$G) && $IsAllocBox(g#0, _module.Iter$G, $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Iter.__ctor(_module.Iter$G: Ty, 
    n#0: int where LitInt(0) <= n#0, 
    g#0: Box
       where $IsBox(g#0, _module.Iter$G) && $IsAllocBox(g#0, _module.Iter$G, $Heap))
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter(_module.Iter$G))
         && $IsAlloc(this, Tclass._module.Iter(_module.Iter$G), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.Iter.n(this) == n#0;
  free ensures true;
  ensures _module.Iter.g(this) == g#0;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Iter.ys), Seq#Empty(): Seq Box);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Iter.ugs), Seq#Empty(): Seq Box);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Iter.zs), Seq#Empty(): Seq Box);
  free ensures _module.Iter.Valid#canCall(_module.Iter$G, $Heap, this);
  ensures _module.Iter.Valid(_module.Iter$G, $Heap, this);
  free ensures true;
  ensures Set#Equal(_module.Iter.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.Iter.__modifies(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.Iter.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.Iter.__decreases0(this) == n#0;
  free ensures true;
  ensures _module.Iter.__decreases1(this) == g#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.Iter.Valid
function _module.Iter.Valid(_module.Iter$G: Ty, $heap: Heap, this: ref) : bool;

function _module.Iter.Valid#canCall(_module.Iter$G: Ty, $heap: Heap, this: ref) : bool;

// frame axiom for _module.Iter.Valid
axiom (forall _module.Iter$G: Ty, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Iter.Valid(_module.Iter$G, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Iter(_module.Iter$G))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.Iter.__reads(this)[$Box($o)]
             || read($h0, this, _module.Iter.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Iter.Valid(_module.Iter$G, $h0, this)
       == _module.Iter.Valid(_module.Iter$G, $h1, this));

// consequence axiom for _module.Iter.Valid
axiom 12 <= $FunctionContextHeight
   ==> (forall _module.Iter$G: Ty, $Heap: Heap, this: ref :: 
    { _module.Iter.Valid(_module.Iter$G, $Heap, this) } 
    _module.Iter.Valid#canCall(_module.Iter$G, $Heap, this)
         || (12 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Iter(_module.Iter$G))
           && $IsAlloc(this, Tclass._module.Iter(_module.Iter$G), $Heap))
       ==> true);

function _module.Iter.Valid#requires(Ty, Heap, ref) : bool;

// #requires axiom for _module.Iter.Valid
axiom (forall _module.Iter$G: Ty, $Heap: Heap, this: ref :: 
  { _module.Iter.Valid#requires(_module.Iter$G, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Iter(_module.Iter$G))
       && $IsAlloc(this, Tclass._module.Iter(_module.Iter$G), $Heap)
     ==> _module.Iter.Valid#requires(_module.Iter$G, $Heap, this) == true);

procedure CheckWellformed$$_module.Iter.Valid(_module.Iter$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter(_module.Iter$G))
         && $IsAlloc(this, Tclass._module.Iter(_module.Iter$G), $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Iter.Valid(_module.Iter$G: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(155,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.Iter.__reads(this)[$Box($o)]
           || read($Heap, this, _module.Iter.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Iter.__new];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



procedure Call$$_module.Iter.MoveNext(_module.Iter$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter(_module.Iter$G))
         && $IsAlloc(this, Tclass._module.Iter(_module.Iter$G), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.Iter.Valid(_module.Iter$G, $Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Iter.__new)[$Box($o)]
         && !read(old($Heap), this, _module.Iter.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.Iter.__new)[$Box(null)];
  free ensures more#0 ==> _module.Iter.Valid#canCall(_module.Iter$G, $Heap, this);
  ensures more#0 ==> _module.Iter.Valid(_module.Iter$G, $Heap, this);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Iter.ys), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.Iter.ys), 
        Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.y)))
       else read(old($Heap), this, _module.Iter.ys)));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Iter.ugs), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.Iter.ugs), 
        Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.ug)))
       else read(old($Heap), this, _module.Iter.ugs)));
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Iter.zs), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.Iter.zs), 
        Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.z)))
       else read(old($Heap), this, _module.Iter.zs)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.Iter.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.Iter.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.Iter: subset type $Is
axiom (forall _module.Iter$G: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.Iter(_module.Iter$G)) } 
  $Is(c#0, Tclass._module.Iter(_module.Iter$G))
     <==> $Is(c#0, Tclass._module.Iter?(_module.Iter$G)) && c#0 != null);

// _module.Iter: subset type $IsAlloc
axiom (forall _module.Iter$G: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Iter(_module.Iter$G), $h) } 
  $IsAlloc(c#0, Tclass._module.Iter(_module.Iter$G), $h)
     <==> $IsAlloc(c#0, Tclass._module.Iter?(_module.Iter$G), $h));

procedure CheckWellformed$$_module.Iter(_module.Iter$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter(_module.Iter$G))
         && $IsAlloc(this, Tclass._module.Iter(_module.Iter$G), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    g#0: Box
       where $IsBox(g#0, _module.Iter$G) && $IsAllocBox(g#0, _module.Iter$G, $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.Iter(_module.Iter$G: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter(_module.Iter$G))
         && $IsAlloc(this, Tclass._module.Iter(_module.Iter$G), $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    g#0: Box
       where $IsBox(g#0, _module.Iter$G) && $IsAllocBox(g#0, _module.Iter$G, $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Iter(_module.Iter$G: Ty, this: ref, n#0: int, g#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int
     where _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ys))
       && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ugs))
       && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.zs));
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $decr_init$loop#01: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $decr$loop#01: int;
  var $obj0: ref;
  var $obj1: ref;
  var $obj2: ref;
  var $rhs#0_0_0: Box where $IsBox($rhs#0_0_0, _module.Iter$G);
  var $rhs#0_0_1: Box where $IsBox($rhs#0_0_1, _module.Iter$G);
  var $rhs#0_0_2: Box where $IsBox($rhs#0_0_2, _module.Iter$G);
  var $rhs#0_1_0: Box where $IsBox($rhs#0_1_0, _module.Iter$G);
  var $rhs#0_1_1: Box where $IsBox($rhs#0_1_1, _module.Iter$G);
  var $rhs#0_2_0_0: Box where $IsBox($rhs#0_2_0_0, _module.Iter$G);
  var $rhs#0_2_0_1: Box where $IsBox($rhs#0_2_0_1, _module.Iter$G);
  var $rhs#0_2_0: Box where $IsBox($rhs#0_2_0, _module.Iter$G);
  var $rhs#0_2_1: Box where $IsBox($rhs#0_2_1, _module.Iter$G);

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(155,9): initial state"} true;
    assume _module.Iter.n(this) == n#0;
    assume _module.Iter.g(this) == g#0;
    assume Seq#Equal(read($Heap, this, _module.Iter.ys), Seq#Empty(): Seq Box);
    assume Seq#Equal(read($Heap, this, _module.Iter.ugs), Seq#Empty(): Seq Box);
    assume Seq#Equal(read($Heap, this, _module.Iter.zs), Seq#Empty(): Seq Box);
    assume _module.Iter.Valid(_module.Iter$G, $Heap, this);
    assume Set#Equal(_module.Iter.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.Iter.__modifies(this), Set#Empty(): Set Box);
    assume Set#Equal(read($Heap, this, _module.Iter.__new), Set#Empty(): Set Box);
    assume _module.Iter.__decreases0(this) == n#0;
    assume _module.Iter.__decreases1(this) == g#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.Iter.__reads(this), read($Heap, this, _module.Iter.__new));
    $_OldIterHeap := $Heap;
    havoc i#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(158,5)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(158,8)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(159,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := _yieldCount#0;
    $decr_init$loop#01 := _module.Iter.n(this) - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      invariant (forall $o: ref :: 
        { read($Heap, this, _module.Iter.__new)[$Box($o)] } 
        read($Heap, this, _module.Iter.__new)[$Box($o)]
           ==> $o != null && !read(old($Heap), $o, alloc));
      free invariant _yieldCount#0 >= $decr_init$loop#00
         && (_yieldCount#0 == $decr_init$loop#00
           ==> _module.Iter.n(this) - i#0 <= $decr_init$loop#01
             && (_module.Iter.n(this) - i#0 == $decr_init$loop#01 ==> true));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(159,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume true;
            assume false;
        }

        assume true;
        if (_module.Iter.n(this) <= i#0)
        {
            break;
        }

        $decr$loop#00 := _yieldCount#0;
        $decr$loop#01 := _module.Iter.n(this) - i#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(161,5)
        assert LitInt(17) != 0;
        assume true;
        if (Mod(i#0, LitInt(17)) == LitInt(0))
        {
            // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(162,7)
            // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(162,7)
            assume true;
            $obj0 := this;
            assert $_Frame[$obj0, _module.Iter.y];
            assume true;
            $obj1 := this;
            assert $_Frame[$obj1, _module.Iter.ug];
            assume true;
            $obj2 := this;
            assert $_Frame[$obj2, _module.Iter.z];
            assume true;
            $rhs#0_0_0 := _module.Iter.g(this);
            assume true;
            $rhs#0_0_1 := _module.Iter.g(this);
            assume true;
            $rhs#0_0_2 := _module.Iter.g(this);
            $Heap := update($Heap, $obj0, _module.Iter.y, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            $Heap := update($Heap, $obj1, _module.Iter.ug, $rhs#0_0_1);
            assume $IsGoodHeap($Heap);
            $Heap := update($Heap, $obj2, _module.Iter.z, $rhs#0_0_2);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(162,19)"} true;
            $Heap := update($Heap, 
              this, 
              _module.Iter.ys, 
              Seq#Append(read($Heap, this, _module.Iter.ys), 
                Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.y))));
            $Heap := update($Heap, 
              this, 
              _module.Iter.ugs, 
              Seq#Append(read($Heap, this, _module.Iter.ugs), 
                Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.ug))));
            $Heap := update($Heap, 
              this, 
              _module.Iter.zs, 
              Seq#Append(read($Heap, this, _module.Iter.zs), 
                Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.z))));
            _yieldCount#0 := _yieldCount#0 + 1;
            assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ys))
               && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ugs))
               && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.zs));
            assume $IsGoodHeap($Heap);
            call $YieldHavoc(this, _module.Iter.__reads(this), read($Heap, this, _module.Iter.__new));
            $_OldIterHeap := $Heap;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(162,19)"} true;
            // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(163,7)
            $Heap := update($Heap, 
              this, 
              _module.Iter.ys, 
              Seq#Append(read($Heap, this, _module.Iter.ys), 
                Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.y))));
            $Heap := update($Heap, 
              this, 
              _module.Iter.ugs, 
              Seq#Append(read($Heap, this, _module.Iter.ugs), 
                Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.ug))));
            $Heap := update($Heap, 
              this, 
              _module.Iter.zs, 
              Seq#Append(read($Heap, this, _module.Iter.zs), 
                Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.z))));
            _yieldCount#0 := _yieldCount#0 + 1;
            assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ys))
               && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ugs))
               && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.zs));
            assume $IsGoodHeap($Heap);
            call $YieldHavoc(this, _module.Iter.__reads(this), read($Heap, this, _module.Iter.__new));
            $_OldIterHeap := $Heap;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(163,11)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(164,12)
            assert LitInt(2) != 0;
            assume true;
            if (i#0 == Div(_module.Iter.n(this), LitInt(2)))
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(165,9)
                assume true;
                assert $_Frame[this, _module.Iter.y];
                assume true;
                $rhs#0_1_0 := _module.Iter.g(this);
                $Heap := update($Heap, this, _module.Iter.y, $rhs#0_1_0);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(165,12)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(166,9)
                assume true;
                assert $_Frame[this, _module.Iter.z];
                assume true;
                $rhs#0_1_1 := read($Heap, this, _module.Iter.y);
                $Heap := update($Heap, this, _module.Iter.z, $rhs#0_1_1);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(166,12)"} true;
                // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(167,7)
                $Heap := update($Heap, 
                  this, 
                  _module.Iter.ys, 
                  Seq#Append(read($Heap, this, _module.Iter.ys), 
                    Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.y))));
                $Heap := update($Heap, 
                  this, 
                  _module.Iter.ugs, 
                  Seq#Append(read($Heap, this, _module.Iter.ugs), 
                    Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.ug))));
                $Heap := update($Heap, 
                  this, 
                  _module.Iter.zs, 
                  Seq#Append(read($Heap, this, _module.Iter.zs), 
                    Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.z))));
                _yieldCount#0 := _yieldCount#0 + 1;
                assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ys))
                   && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ugs))
                   && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.zs));
                assume $IsGoodHeap($Heap);
                call $YieldHavoc(this, _module.Iter.__reads(this), read($Heap, this, _module.Iter.__new));
                $_OldIterHeap := $Heap;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(167,11)"} true;
                // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(168,7)
                $Heap := update($Heap, 
                  this, 
                  _module.Iter.ys, 
                  Seq#Append(read($Heap, this, _module.Iter.ys), 
                    Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.y))));
                $Heap := update($Heap, 
                  this, 
                  _module.Iter.ugs, 
                  Seq#Append(read($Heap, this, _module.Iter.ugs), 
                    Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.ug))));
                $Heap := update($Heap, 
                  this, 
                  _module.Iter.zs, 
                  Seq#Append(read($Heap, this, _module.Iter.zs), 
                    Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.z))));
                _yieldCount#0 := _yieldCount#0 + 1;
                assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ys))
                   && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ugs))
                   && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.zs));
                assume $IsGoodHeap($Heap);
                call $YieldHavoc(this, _module.Iter.__reads(this), read($Heap, this, _module.Iter.__new));
                $_OldIterHeap := $Heap;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(168,11)"} true;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(169,12)
                assert LitInt(11) != 0;
                assume true;
                if (i#0 == Mod(_module.Iter.n(this), LitInt(11)))
                {
                    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(170,7)
                    if (*)
                    {
                        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(171,15)
                        assume true;
                        $obj0 := this;
                        assert $_Frame[$obj0, _module.Iter.ug];
                        assume true;
                        $obj1 := this;
                        assert $_Frame[$obj1, _module.Iter.y];
                        assume true;
                        $rhs#0_2_0_0 := _module.Iter.g(this);
                        assume true;
                        $rhs#0_2_0_1 := _module.Iter.g(this);
                        $Heap := update($Heap, $obj0, _module.Iter.ug, $rhs#0_2_0_0);
                        assume $IsGoodHeap($Heap);
                        $Heap := update($Heap, $obj1, _module.Iter.y, $rhs#0_2_0_1);
                        assume $IsGoodHeap($Heap);
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(171,21)"} true;
                        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(172,9)
                        $Heap := update($Heap, 
                          this, 
                          _module.Iter.ys, 
                          Seq#Append(read($Heap, this, _module.Iter.ys), 
                            Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.y))));
                        $Heap := update($Heap, 
                          this, 
                          _module.Iter.ugs, 
                          Seq#Append(read($Heap, this, _module.Iter.ugs), 
                            Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.ug))));
                        $Heap := update($Heap, 
                          this, 
                          _module.Iter.zs, 
                          Seq#Append(read($Heap, this, _module.Iter.zs), 
                            Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.z))));
                        _yieldCount#0 := _yieldCount#0 + 1;
                        assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ys))
                           && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ugs))
                           && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.zs));
                        assume $IsGoodHeap($Heap);
                        call $YieldHavoc(this, _module.Iter.__reads(this), read($Heap, this, _module.Iter.__new));
                        $_OldIterHeap := $Heap;
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(172,13)"} true;
                    }
                    else
                    {
                        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(174,11)
                        assume true;
                        assert $_Frame[this, _module.Iter.y];
                        assume true;
                        $rhs#0_2_0 := _module.Iter.g(this);
                        $Heap := update($Heap, this, _module.Iter.y, $rhs#0_2_0);
                        assume $IsGoodHeap($Heap);
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(174,14)"} true;
                        // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(175,9)
                        $Heap := update($Heap, 
                          this, 
                          _module.Iter.ys, 
                          Seq#Append(read($Heap, this, _module.Iter.ys), 
                            Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.y))));
                        $Heap := update($Heap, 
                          this, 
                          _module.Iter.ugs, 
                          Seq#Append(read($Heap, this, _module.Iter.ugs), 
                            Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.ug))));
                        $Heap := update($Heap, 
                          this, 
                          _module.Iter.zs, 
                          Seq#Append(read($Heap, this, _module.Iter.zs), 
                            Seq#Build(Seq#Empty(): Seq Box, read($Heap, this, _module.Iter.z))));
                        _yieldCount#0 := _yieldCount#0 + 1;
                        assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ys))
                           && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.ugs))
                           && _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter.zs));
                        assume $IsGoodHeap($Heap);
                        call $YieldHavoc(this, _module.Iter.__reads(this), read($Heap, this, _module.Iter.__new));
                        $_OldIterHeap := $Heap;
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(175,13)"} true;
                    }

                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(177,9)
                    assume true;
                    assert $_Frame[this, _module.Iter.y];
                    assert LitInt(2) != 0;
                    if (Mod(i#0, LitInt(2)) == LitInt(0))
                    {
                    }
                    else
                    {
                    }

                    assume true;
                    $rhs#0_2_1 := (if Mod(i#0, LitInt(2)) == LitInt(0)
                       then read($Heap, this, _module.Iter.y)
                       else read($Heap, this, _module.Iter.y));
                    $Heap := update($Heap, this, _module.Iter.y, $rhs#0_2_1);
                    assume $IsGoodHeap($Heap);
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(177,38)"} true;
                }
                else
                {
                }
            }
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(179,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(179,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(159,3)
        assert 0 <= $decr$loop#01
           || _yieldCount#0 > $decr$loop#00
           || _module.Iter.n(this) - i#0 == $decr$loop#01;
        assert _yieldCount#0 > $decr$loop#00
           || (_yieldCount#0 == $decr$loop#00 && _module.Iter.n(this) - i#0 < $decr$loop#01);
    }
}



const unique class._module.Regression213?: ClassName;

function Tclass._module.Regression213?() : Ty;

const unique Tagclass._module.Regression213?: TyTag;

// Tclass._module.Regression213? Tag
axiom Tag(Tclass._module.Regression213?()) == Tagclass._module.Regression213?
   && TagFamily(Tclass._module.Regression213?()) == tytagFamily$Regression213;

// Box/unbox axiom for Tclass._module.Regression213?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Regression213?()) } 
  $IsBox(bx, Tclass._module.Regression213?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Regression213?()));

// Regression213: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Regression213?()) } 
  $Is($o, Tclass._module.Regression213?())
     <==> $o == null || dtype($o) == Tclass._module.Regression213?());

// Regression213: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Regression213?(), $h) } 
  $IsAlloc($o, Tclass._module.Regression213?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.Regression213() : Ty;

const unique Tagclass._module.Regression213: TyTag;

// Tclass._module.Regression213 Tag
axiom Tag(Tclass._module.Regression213()) == Tagclass._module.Regression213
   && TagFamily(Tclass._module.Regression213()) == tytagFamily$Regression213;

// Box/unbox axiom for Tclass._module.Regression213
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Regression213()) } 
  $IsBox(bx, Tclass._module.Regression213())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.Regression213()));

procedure CheckWellformed$$_module.Regression213.A(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Regression213.A()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Regression213.A()
   returns (this: ref where this != null && $Is(this, Tclass._module.Regression213()), 
    $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.Regression213.B(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Regression213.B()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Regression213.B()
   returns (this: ref where this != null && $Is(this, Tclass._module.Regression213()), 
    $_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.Regression213.C(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Regression213.C()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Regression213.C()
   returns (this: ref where this != null && $Is(this, Tclass._module.Regression213()), 
    $_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Regression213.C() returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#f#0: bool;
  var f#0: ref
     where defass#f#0
       ==> $Is(f#0, Tclass._System.object())
         && $IsAlloc(f#0, Tclass._System.object(), $Heap);
  var g#0: ref
     where $Is(g#0, Tclass._System.object())
       && $IsAlloc(g#0, Tclass._System.object(), $Heap);

    // AddMethodImpl: C, Impl$$_module.Regression213.C
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(274,18): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(274,19)
    havoc f#0 /* where defass#f#0
       ==> $Is(f#0, Tclass._System.object())
         && $IsAlloc(f#0, Tclass._System.object(), $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(276,11)
    assume true;
    assert defass#f#0;
    assume true;
    g#0 := f#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(276,14)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(274,19)
    assume !read($Heap, this, alloc);
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(274,19)
}



procedure CheckWellformed$$_module.Regression213.D(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Regression213.D()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Regression213.D()
   returns (this: ref where this != null && $Is(this, Tclass._module.Regression213()), 
    $_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Regression213.D() returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#f#0: bool;
  var f#0: ref
     where defass#f#0
       ==> $Is(f#0, Tclass._System.object())
         && $IsAlloc(f#0, Tclass._System.object(), $Heap);
  var g#0: ref
     where $Is(g#0, Tclass._System.object())
       && $IsAlloc(g#0, Tclass._System.object(), $Heap);

    // AddMethodImpl: D, Impl$$_module.Regression213.D
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(278,18): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(278,19)
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(278,19)
    assume !read($Heap, this, alloc);
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(278,19)
    havoc f#0 /* where defass#f#0
       ==> $Is(f#0, Tclass._System.object())
         && $IsAlloc(f#0, Tclass._System.object(), $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(281,11)
    assume true;
    assert defass#f#0;
    assume true;
    g#0 := f#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(281,14)"} true;
}



procedure CheckWellformed$$_module.Regression213.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Regression213.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Regression213.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.Regression213.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Regression213.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Regression213.N(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Regression213())
         && $IsAlloc(this, Tclass._module.Regression213(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Regression213.N(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#f#0: bool;
  var f#0: ref
     where defass#f#0
       ==> $Is(f#0, Tclass._System.object())
         && $IsAlloc(f#0, Tclass._System.object(), $Heap);
  var g#0: ref
     where $Is(g#0, Tclass._System.object())
       && $IsAlloc(g#0, Tclass._System.object(), $Heap);

    // AddMethodImpl: N, Impl$$_module.Regression213.N
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(287,13): initial state"} true;
    $_reverifyPost := false;
    havoc f#0 /* where defass#f#0
       ==> $Is(f#0, Tclass._System.object())
         && $IsAlloc(f#0, Tclass._System.object(), $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(289,11)
    assume true;
    assert defass#f#0;
    assume true;
    g#0 := f#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(289,14)"} true;
}



// _module.Regression213: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Regression213()) } 
  $Is(c#0, Tclass._module.Regression213())
     <==> $Is(c#0, Tclass._module.Regression213?()) && c#0 != null);

// _module.Regression213: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Regression213(), $h) } 
  $IsAlloc(c#0, Tclass._module.Regression213(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Regression213?(), $h));

const unique class._module.__default: ClassName;

function Tclass._module.__default() : Ty;

const unique Tagclass._module.__default: TyTag;

// Tclass._module.__default Tag
axiom Tag(Tclass._module.__default()) == Tagclass._module.__default
   && TagFamily(Tclass._module.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass._module.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.__default()) } 
  $IsBox(bx, Tclass._module.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.__default()) } 
  $Is($o, Tclass._module.__default())
     <==> $o == null || dtype($o) == Tclass._module.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.__default(), $h) } 
  $IsAlloc($o, Tclass._module.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$_module.__default.M0(_module._default.M0$G: Ty, 
    x#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.M0$G)
         && $IsAllocBox(a#0, _module._default.M0$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.M0$G)
         && $IsAllocBox(b#0, _module._default.M0$G, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module._default.M0$G)
         && $IsAllocBox(y#0, _module._default.M0$G, $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M0(_module._default.M0$G: Ty, 
    x#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.M0$G)
         && $IsAllocBox(a#0, _module._default.M0$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.M0$G)
         && $IsAllocBox(b#0, _module._default.M0$G, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module._default.M0$G)
         && $IsAllocBox(y#0, _module._default.M0$G, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M0(_module._default.M0$G: Ty, 
    x#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.M0$G)
         && $IsAllocBox(a#0, _module._default.M0$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.M0$G)
         && $IsAllocBox(b#0, _module._default.M0$G, $Heap))
   returns (defass#y#0: bool, 
    y#0: Box
       where defass#y#0
         ==> $IsBox(y#0, _module._default.M0$G)
           && $IsAllocBox(y#0, _module._default.M0$G, $Heap), 
    $_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M0(_module._default.M0$G: Ty, x#0: int, a#0: Box, b#0: Box)
   returns (defass#y#0: bool, y#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M0, Impl$$_module.__default.M0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(32,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(33,3)
    assume true;
    if (x#0 < 10)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(34,7)
        assume true;
        assume true;
        y#0 := a#0;
        defass#y#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(34,10)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(35,10)
        assume true;
        if (x#0 < 100)
        {
            // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(36,5)
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(36,5)
            assume true;
            assume true;
            y#0 := b#0;
            defass#y#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(36,12)"} true;
            assert defass#y#0;
            return;
        }
        else
        {
        }
    }

    assert defass#y#0;
}



procedure CheckWellformed$$_module.__default.M1(_module._default.M1$G: Ty, 
    x#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.M1$G)
         && $IsAllocBox(a#0, _module._default.M1$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.M1$G)
         && $IsAllocBox(b#0, _module._default.M1$G, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module._default.M1$G)
         && $IsAllocBox(y#0, _module._default.M1$G, $Heap), 
    z#0: Box
       where $IsBox(z#0, _module._default.M1$G)
         && $IsAllocBox(z#0, _module._default.M1$G, $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M1(_module._default.M1$G: Ty, 
    x#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.M1$G)
         && $IsAllocBox(a#0, _module._default.M1$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.M1$G)
         && $IsAllocBox(b#0, _module._default.M1$G, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module._default.M1$G)
         && $IsAllocBox(y#0, _module._default.M1$G, $Heap), 
    z#0: Box
       where $IsBox(z#0, _module._default.M1$G)
         && $IsAllocBox(z#0, _module._default.M1$G, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M1(_module._default.M1$G: Ty, 
    x#0: int, 
    a#0: Box
       where $IsBox(a#0, _module._default.M1$G)
         && $IsAllocBox(a#0, _module._default.M1$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.M1$G)
         && $IsAllocBox(b#0, _module._default.M1$G, $Heap))
   returns (defass#y#0: bool, 
    y#0: Box
       where defass#y#0
         ==> $IsBox(y#0, _module._default.M1$G)
           && $IsAllocBox(y#0, _module._default.M1$G, $Heap), 
    defass#z#0: bool, 
    z#0: Box
       where defass#z#0
         ==> $IsBox(z#0, _module._default.M1$G)
           && $IsAllocBox(z#0, _module._default.M1$G, $Heap), 
    $_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M1(_module._default.M1$G: Ty, x#0: int, a#0: Box, b#0: Box)
   returns (defass#y#0: bool, y#0: Box, defass#z#0: bool, z#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0_0: Box where $IsBox($rhs#0_0, _module._default.M1$G);
  var $rhs#0_1: Box where $IsBox($rhs#0_1, _module._default.M1$G);
  var i#2_0: Box
     where $IsBox(i#2_0, _module._default.M1$G)
       && $IsAllocBox(i#2_0, _module._default.M1$G, $Heap);
  var j#2_0: Box
     where $IsBox(j#2_0, _module._default.M1$G)
       && $IsAllocBox(j#2_0, _module._default.M1$G, $Heap);
  var $rhs#2_0: Box where $IsBox($rhs#2_0, _module._default.M1$G);
  var $rhs#2_1: Box where $IsBox($rhs#2_1, _module._default.M1$G);
  var $rhs#2_2: Box where $IsBox($rhs#2_2, _module._default.M1$G);
  var $rhs#2_3: Box where $IsBox($rhs#2_3, _module._default.M1$G);
  var defass#i#3_0: bool;
  var i#3_0: Box
     where defass#i#3_0
       ==> $IsBox(i#3_0, _module._default.M1$G)
         && $IsAllocBox(i#3_0, _module._default.M1$G, $Heap);
  var defass#j#3_0: bool;
  var j#3_0: Box
     where defass#j#3_0
       ==> $IsBox(j#3_0, _module._default.M1$G)
         && $IsAllocBox(j#3_0, _module._default.M1$G, $Heap);
  var $rhs#3_0: Box where $IsBox($rhs#3_0, _module._default.M1$G);
  var $rhs#3_1: Box where $IsBox($rhs#3_1, _module._default.M1$G);

    // AddMethodImpl: M1, Impl$$_module.__default.M1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(44,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(45,3)
    assume true;
    if (x#0 < 10)
    {
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(46,10)
        assume true;
        assume true;
        assume true;
        $rhs#0_0 := a#0;
        assume true;
        $rhs#0_1 := a#0;
        z#0 := $rhs#0_0;
        defass#z#0 := true;
        y#0 := $rhs#0_1;
        defass#y#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(46,16)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(47,10)
        assume true;
        if (x#0 < 20)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(48,7)
            assume true;
            assert defass#z#0;
            assume true;
            y#0 := z#0;
            defass#y#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(48,10)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(49,7)
            assume true;
            assume true;
            z#0 := a#0;
            defass#z#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(49,10)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(50,10)
            assume true;
            if (x#0 < 30)
            {
                // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(51,14)
                assume true;
                assume true;
                assume true;
                $rhs#2_0 := a#0;
                assume true;
                $rhs#2_1 := b#0;
                i#2_0 := $rhs#2_0;
                j#2_0 := $rhs#2_1;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(51,20)"} true;
                // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(52,10)
                assume true;
                assume true;
                assume true;
                $rhs#2_2 := i#2_0;
                assume true;
                $rhs#2_3 := j#2_0;
                y#0 := $rhs#2_2;
                defass#y#0 := true;
                z#0 := $rhs#2_3;
                defass#z#0 := true;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(52,16)"} true;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(53,10)
                assume true;
                if (x#0 < 40)
                {
                    havoc i#3_0 /* where defass#i#3_0
                       ==> $IsBox(i#3_0, _module._default.M1$G)
                         && $IsAllocBox(i#3_0, _module._default.M1$G, $Heap) */, j#3_0 /* where defass#j#3_0
                       ==> $IsBox(j#3_0, _module._default.M1$G)
                         && $IsAllocBox(j#3_0, _module._default.M1$G, $Heap) */;
                    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(55,7)
                    assume true;
                    assume true;
                    i#3_0 := a#0;
                    defass#i#3_0 := true;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(55,10)"} true;
                    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(56,10)
                    assume true;
                    assume true;
                    assert defass#i#3_0;
                    assume true;
                    $rhs#3_0 := i#3_0;
                    assert defass#j#3_0;
                    assume true;
                    $rhs#3_1 := j#3_0;
                    y#0 := $rhs#3_0;
                    defass#y#0 := true;
                    z#0 := $rhs#3_1;
                    defass#z#0 := true;
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(56,16)"} true;
                }
                else
                {
                    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(57,10)
                    assume true;
                    if (x#0 < 100)
                    {
                        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(58,7)
                        assume true;
                        assume true;
                        z#0 := a#0;
                        defass#z#0 := true;
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(58,10)"} true;
                        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(59,5)
                        assert defass#y#0;
                        assert defass#z#0;
                        return;
                    }
                    else
                    {
                        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(61,7)
                        assume true;
                        assume true;
                        y#0 := b#0;
                        defass#y#0 := true;
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(61,10)"} true;
                    }
                }
            }
        }
    }

    assert defass#y#0;
    assert defass#z#0;
}



// function declaration for _module._default.F
function _module.__default.F() : ref;

function _module.__default.F#canCall() : bool;

// consequence axiom for _module.__default.F
axiom 3 <= $FunctionContextHeight
   ==> 
  _module.__default.F#canCall() || 3 != $FunctionContextHeight
   ==> $Is(_module.__default.F(), Tclass._module.C());

function _module.__default.F#requires() : bool;

// #requires axiom for _module.__default.F
axiom _module.__default.F#requires() == true;

procedure CheckWellformed$$_module.__default.F();
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default._default_Main();
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default._default_Main();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default._default_Main() returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default._default_Main() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.NonNullC())
       && $IsAlloc(c#0, Tclass._module.NonNullC(), $Heap);
  var $nw: ref;
  var y#0: ref
     where $Is(y#0, Tclass._module.NonNullC())
       && $IsAlloc(y#0, Tclass._module.NonNullC(), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.NonNullC())
       && $IsAlloc($rhs##0, Tclass._module.NonNullC(), $Heap);
  var x##0: int;
  var a##0: ref;
  var b##0: ref;
  var $tmp##0: Box;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(72,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(73,19)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.C?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    assert $Is($nw, Tclass._module.NonNullC());
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(73,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(74,24)
    assume true;
    // TrCallStmt: Adding lhs with type NonNullC
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(102);
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    b##0 := c#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##0 := Call$$_module.__default.M0(Tclass._module.NonNullC(), x##0, $Box(a##0), $Box(b##0));
    havoc $rhs##0;
    assume $rhs##0 == $Unbox($tmp##0): ref;
    // TrCallStmt: After ProcessCallStmt
    y#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(74,34)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(75,3)
    assume true;
    assert y#0 != null;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(76,3)
    assert {:subsumption 0} y#0 != null;
    assume true;
    assume true;
}



procedure CheckWellformed$$_module.__default.DontForgetHavoc(_module._default.DontForgetHavoc$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.DontForgetHavoc$G)
         && $IsAllocBox(a#0, _module._default.DontForgetHavoc$G, $Heap), 
    h#0: int)
   returns (k#0: Box
       where $IsBox(k#0, _module._default.DontForgetHavoc$G)
         && $IsAllocBox(k#0, _module._default.DontForgetHavoc$G, $Heap));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.DontForgetHavoc(_module._default.DontForgetHavoc$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.DontForgetHavoc$G)
         && $IsAllocBox(a#0, _module._default.DontForgetHavoc$G, $Heap), 
    h#0: int)
   returns (k#0: Box
       where $IsBox(k#0, _module._default.DontForgetHavoc$G)
         && $IsAllocBox(k#0, _module._default.DontForgetHavoc$G, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.DontForgetHavoc(_module._default.DontForgetHavoc$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.DontForgetHavoc$G)
         && $IsAllocBox(a#0, _module._default.DontForgetHavoc$G, $Heap), 
    h#0: int)
   returns (defass#k#0: bool, 
    k#0: Box
       where defass#k#0
         ==> $IsBox(k#0, _module._default.DontForgetHavoc$G)
           && $IsAllocBox(k#0, _module._default.DontForgetHavoc$G, $Heap), 
    $_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.DontForgetHavoc(_module._default.DontForgetHavoc$G: Ty, a#0: Box, h#0: int)
   returns (defass#k#0: bool, k#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: Box
     where $IsBox(x#0, _module._default.DontForgetHavoc$G)
       && $IsAllocBox(x#0, _module._default.DontForgetHavoc$G, $Heap);
  var defass#y#0: bool;
  var y#0: Box
     where defass#y#0
       ==> $IsBox(y#0, _module._default.DontForgetHavoc$G)
         && $IsAllocBox(y#0, _module._default.DontForgetHavoc$G, $Heap);
  var z#0: Box
     where $IsBox(z#0, _module._default.DontForgetHavoc$G)
       && $IsAllocBox(z#0, _module._default.DontForgetHavoc$G, $Heap);
  var $rhs#0: Box where $IsBox($rhs#0, _module._default.DontForgetHavoc$G);
  var $rhs#1: Box where $IsBox($rhs#1, _module._default.DontForgetHavoc$G);
  var $rhs#2: Box where $IsBox($rhs#2, _module._default.DontForgetHavoc$G);

    // AddMethodImpl: DontForgetHavoc, Impl$$_module.__default.DontForgetHavoc
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(80,55): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(81,21)
    assume true;
    assume true;
    assume true;
    assume true;
    $rhs#0 := a#0;
    havoc $rhs#1 /* where $IsBox($rhs#1, _module._default.DontForgetHavoc$G) */;
    assume true;
    $rhs#2 := a#0;
    x#0 := $rhs#0;
    y#0 := $rhs#1;
    z#0 := $rhs#2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(81,30)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(82,3)
    assume true;
    if (h#0 < 10)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(83,7)
        assume true;
        assume true;
        k#0 := x#0;
        defass#k#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(83,10)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(84,10)
        assume true;
        if (h#0 < 20)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(85,7)
            assume true;
            assert defass#y#0;
            assume true;
            k#0 := y#0;
            defass#k#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(85,10)"} true;
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(87,7)
            assume true;
            havoc z#0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(87,10)"} true;
            // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(88,5)
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(88,5)
            assume true;
            assume true;
            k#0 := z#0;
            defass#k#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(88,12)"} true;
            assert defass#k#0;
            return;
        }
    }

    assert defass#k#0;
}



procedure CheckWellformed$$_module.__default.OtherAssignments(_module._default.OtherAssignments$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(a#0, _module._default.OtherAssignments$G, $Heap), 
    h#0: int)
   returns (k#0: Box
       where $IsBox(k#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(k#0, _module._default.OtherAssignments$G, $Heap));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.OtherAssignments(_module._default.OtherAssignments$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(a#0, _module._default.OtherAssignments$G, $Heap), 
    h#0: int)
   returns (k#0: Box
       where $IsBox(k#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(k#0, _module._default.OtherAssignments$G, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.OtherAssignments(_module._default.OtherAssignments$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(a#0, _module._default.OtherAssignments$G, $Heap), 
    h#0: int)
   returns (defass#k#0: bool, 
    k#0: Box
       where defass#k#0
         ==> $IsBox(k#0, _module._default.OtherAssignments$G)
           && $IsAllocBox(k#0, _module._default.OtherAssignments$G, $Heap), 
    $_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.OtherAssignments(_module._default.OtherAssignments$G: Ty, a#0: Box, h#0: int)
   returns (defass#k#0: bool, k#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#e0#0: bool;
  var e0#0: Box
     where defass#e0#0
       ==> $IsBox(e0#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(e0#0, _module._default.OtherAssignments$G, $Heap);
  var defass#e1#0: bool;
  var e1#0: Box
     where defass#e1#0
       ==> $IsBox(e1#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(e1#0, _module._default.OtherAssignments$G, $Heap);
  var e0#1: Box;
  var defass#x#0: bool;
  var x#0: Box
     where defass#x#0
       ==> $IsBox(x#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(x#0, _module._default.OtherAssignments$G, $Heap);
  var defass#y#0: bool;
  var y#0: Box
     where defass#y#0
       ==> $IsBox(y#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(y#0, _module._default.OtherAssignments$G, $Heap);
  var defass#z#0: bool;
  var z#0: Box
     where defass#z#0
       ==> $IsBox(z#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(z#0, _module._default.OtherAssignments$G, $Heap);
  var x#1: Box;
  var y#1: Box;
  var z#1: Box;

    // AddMethodImpl: OtherAssignments, Impl$$_module.__default.OtherAssignments
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(92,60): initial state"} true;
    $_reverifyPost := false;
    havoc e0#0 /* where defass#e0#0
       ==> $IsBox(e0#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(e0#0, _module._default.OtherAssignments$G, $Heap) */, e1#0 /* where defass#e1#0
       ==> $IsBox(e1#0, _module._default.OtherAssignments$G)
         && $IsAllocBox(e1#0, _module._default.OtherAssignments$G, $Heap) */;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(94,6)
    havoc e0#1;
    if ($IsBox(e0#1, _module._default.OtherAssignments$G)
       && $IsAllocBox(e0#1, _module._default.OtherAssignments$G, $Heap))
    {
        assert defass#e1#0;
        assume true;
    }

    assert ($IsBox(e1#0, _module._default.OtherAssignments$G) && e1#0 == e1#0)
       || (exists $as#e00#0: Box :: 
        $IsBox($as#e00#0, _module._default.OtherAssignments$G) && $as#e00#0 == e1#0);
    defass#e0#0 := true;
    havoc e0#0;
    assume e0#0 == e1#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(94,16)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(95,21)
    havoc x#1;
    havoc y#1;
    havoc z#1;
    if ($IsBox(x#1, _module._default.OtherAssignments$G)
       && $IsAllocBox(x#1, _module._default.OtherAssignments$G, $Heap)
       && 
      $IsBox(y#1, _module._default.OtherAssignments$G)
       && $IsAllocBox(y#1, _module._default.OtherAssignments$G, $Heap)
       && 
      $IsBox(z#1, _module._default.OtherAssignments$G)
       && $IsAllocBox(z#1, _module._default.OtherAssignments$G, $Heap))
    {
        if (x#1 == z#1)
        {
        }

        assume true;
    }

    assert (exists $as#y0#0: Box :: 
        $IsBox($as#y0#0, _module._default.OtherAssignments$G)
           && 
          $IsBox(a#0, _module._default.OtherAssignments$G)
           && $IsBox(a#0, _module._default.OtherAssignments$G)
           && 
          a#0 == a#0
           && a#0 == a#0)
       || 
      (exists $as#x0#0: Box, $as#y0#0: Box :: 
        $IsBox($as#x0#0, _module._default.OtherAssignments$G)
           && $IsBox($as#y0#0, _module._default.OtherAssignments$G)
           && 
          $IsBox(a#0, _module._default.OtherAssignments$G)
           && 
          $as#x0#0 == a#0
           && a#0 == a#0)
       || 
      (exists $as#y0#0: Box :: 
        $IsBox($as#y0#0, _module._default.OtherAssignments$G)
           && 
          $IsBox(a#0, _module._default.OtherAssignments$G)
           && $IsBox(a#0, _module._default.OtherAssignments$G)
           && 
          a#0 == a#0
           && a#0 == a#0)
       || 
      (exists $as#x0#0: Box, $as#y0#0: Box :: 
        $IsBox($as#x0#0, _module._default.OtherAssignments$G)
           && $IsBox($as#y0#0, _module._default.OtherAssignments$G)
           && 
          $IsBox($as#x0#0, _module._default.OtherAssignments$G)
           && 
          $as#x0#0 == $as#x0#0
           && $as#x0#0 == a#0)
       || 
      (exists $as#y0#0: Box, $as#z0#0: Box :: 
        $IsBox($as#y0#0, _module._default.OtherAssignments$G)
           && $IsBox($as#z0#0, _module._default.OtherAssignments$G)
           && 
          $IsBox($as#z0#0, _module._default.OtherAssignments$G)
           && 
          $as#z0#0 == $as#z0#0
           && $as#z0#0 == a#0)
       || (exists $as#x0#0: Box, $as#y0#0: Box, $as#z0#0: Box :: 
        $IsBox($as#x0#0, _module._default.OtherAssignments$G)
           && $IsBox($as#y0#0, _module._default.OtherAssignments$G)
           && $IsBox($as#z0#0, _module._default.OtherAssignments$G)
           && 
          $as#x0#0 == $as#z0#0
           && $as#z0#0 == a#0);
    defass#x#0 := true;
    defass#y#0 := true;
    defass#z#0 := true;
    havoc x#0, y#0, z#0;
    assume x#0 == z#0 && z#0 == a#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(95,34)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(97,3)
    assume true;
    if (h#0 < 10)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(98,7)
        assume true;
        assert defass#x#0;
        assume true;
        k#0 := x#0;
        defass#k#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(98,10)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(99,10)
        assume true;
        if (h#0 < 20)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(100,7)
            assume true;
            assert defass#y#0;
            assume true;
            k#0 := y#0;
            defass#k#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(100,10)"} true;
        }
        else
        {
            // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(102,5)
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(102,5)
            assume true;
            assert defass#z#0;
            assume true;
            k#0 := z#0;
            defass#k#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(102,12)"} true;
            assert defass#k#0;
            return;
        }
    }

    assert defass#k#0;
}



procedure CheckWellformed$$_module.__default.OtherAssignments_k(_module._default.OtherAssignments'$G: Ty);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.OtherAssignments_k(_module._default.OtherAssignments'$G: Ty);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.OtherAssignments_k(_module._default.OtherAssignments'$G: Ty) returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.OtherAssignments_k(_module._default.OtherAssignments'$G: Ty) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var e0#0: Box
     where $IsBox(e0#0, _module._default.OtherAssignments'$G)
       && $IsAllocBox(e0#0, _module._default.OtherAssignments'$G, $Heap);
  var e1#0: Box
     where $IsBox(e1#0, _module._default.OtherAssignments'$G)
       && $IsAllocBox(e1#0, _module._default.OtherAssignments'$G, $Heap);
  var e0#1: Box;

    // AddMethodImpl: OtherAssignments', Impl$$_module.__default.OtherAssignments_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(105,36): initial state"} true;
    $_reverifyPost := false;
    havoc e0#0 /* where $IsBox(e0#0, _module._default.OtherAssignments'$G)
       && $IsAllocBox(e0#0, _module._default.OtherAssignments'$G, $Heap) */, e1#0 /* where $IsBox(e1#0, _module._default.OtherAssignments'$G)
       && $IsAllocBox(e1#0, _module._default.OtherAssignments'$G, $Heap) */;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(107,6)
    havoc e0#1;
    if ($IsBox(e0#1, _module._default.OtherAssignments'$G)
       && $IsAllocBox(e0#1, _module._default.OtherAssignments'$G, $Heap))
    {
        assume true;
    }

    assert ($IsBox(e1#0, _module._default.OtherAssignments'$G) && e1#0 == e1#0)
       || (exists $as#e00#0: Box :: 
        $IsBox($as#e00#0, _module._default.OtherAssignments'$G) && $as#e00#0 == e1#0);
    havoc e0#0;
    assume e0#0 == e1#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(107,16)"} true;
}



procedure CheckWellformed$$_module.__default.Callee(_module._default.Callee$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.Callee$G)
         && $IsAllocBox(a#0, _module._default.Callee$G, $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module._default.Callee$G)
         && $IsAllocBox(x#0, _module._default.Callee$G, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.Callee$G)
         && $IsAllocBox(y#0, _module._default.Callee$G, $Heap), 
    z#0: Box
       where $IsBox(z#0, _module._default.Callee$G)
         && $IsAllocBox(z#0, _module._default.Callee$G, $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Callee(_module._default.Callee$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.Callee$G)
         && $IsAllocBox(a#0, _module._default.Callee$G, $Heap))
   returns (x#0: Box
       where $IsBox(x#0, _module._default.Callee$G)
         && $IsAllocBox(x#0, _module._default.Callee$G, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.Callee$G)
         && $IsAllocBox(y#0, _module._default.Callee$G, $Heap), 
    z#0: Box
       where $IsBox(z#0, _module._default.Callee$G)
         && $IsAllocBox(z#0, _module._default.Callee$G, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Callee(_module._default.Callee$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.Callee$G)
         && $IsAllocBox(a#0, _module._default.Callee$G, $Heap))
   returns (defass#x#0: bool, 
    x#0: Box
       where defass#x#0
         ==> $IsBox(x#0, _module._default.Callee$G)
           && $IsAllocBox(x#0, _module._default.Callee$G, $Heap), 
    defass#y#0: bool, 
    y#0: Box
       where defass#y#0
         ==> $IsBox(y#0, _module._default.Callee$G)
           && $IsAllocBox(y#0, _module._default.Callee$G, $Heap), 
    defass#z#0: bool, 
    z#0: Box
       where defass#z#0
         ==> $IsBox(z#0, _module._default.Callee$G)
           && $IsAllocBox(z#0, _module._default.Callee$G, $Heap), 
    $_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Callee(_module._default.Callee$G: Ty, a#0: Box)
   returns (defass#x#0: bool, 
    x#0: Box, 
    defass#y#0: bool, 
    y#0: Box, 
    defass#z#0: bool, 
    z#0: Box, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Box where $IsBox($rhs#0, _module._default.Callee$G);
  var $rhs#1: Box where $IsBox($rhs#1, _module._default.Callee$G);
  var $rhs#2: Box where $IsBox($rhs#2, _module._default.Callee$G);

    // AddMethodImpl: Callee, Impl$$_module.__default.Callee
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(109,50): initial state"} true;
    $_reverifyPost := false;
    // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(110,3)
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(110,3)
    assume true;
    assume true;
    assume true;
    assume true;
    $rhs#0 := a#0;
    assume true;
    $rhs#1 := a#0;
    assume true;
    $rhs#2 := a#0;
    x#0 := $rhs#0;
    defass#x#0 := true;
    y#0 := $rhs#1;
    defass#y#0 := true;
    z#0 := $rhs#2;
    defass#z#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(110,16)"} true;
    assert defass#x#0;
    assert defass#y#0;
    assert defass#z#0;
    return;

    assert defass#x#0;
    assert defass#y#0;
    assert defass#z#0;
}



procedure CheckWellformed$$_module.__default.Caller(_module._default.Caller$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module._default.Caller$G)
         && $IsAllocBox(g#0, _module._default.Caller$G, $Heap))
   returns (k#0: Box
       where $IsBox(k#0, _module._default.Caller$G)
         && $IsAllocBox(k#0, _module._default.Caller$G, $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Caller(_module._default.Caller$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module._default.Caller$G)
         && $IsAllocBox(g#0, _module._default.Caller$G, $Heap))
   returns (k#0: Box
       where $IsBox(k#0, _module._default.Caller$G)
         && $IsAllocBox(k#0, _module._default.Caller$G, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Caller(_module._default.Caller$G: Ty, 
    g#0: Box
       where $IsBox(g#0, _module._default.Caller$G)
         && $IsAllocBox(g#0, _module._default.Caller$G, $Heap))
   returns (defass#k#0: bool, 
    k#0: Box
       where defass#k#0
         ==> $IsBox(k#0, _module._default.Caller$G)
           && $IsAllocBox(k#0, _module._default.Caller$G, $Heap), 
    $_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Caller(_module._default.Caller$G: Ty, g#0: Box)
   returns (defass#k#0: bool, k#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Box
     where $IsBox(a#0, _module._default.Caller$G)
       && $IsAllocBox(a#0, _module._default.Caller$G, $Heap);
  var b#0: Box
     where $IsBox(b#0, _module._default.Caller$G)
       && $IsAllocBox(b#0, _module._default.Caller$G, $Heap);
  var c#0: Box
     where $IsBox(c#0, _module._default.Caller$G)
       && $IsAllocBox(c#0, _module._default.Caller$G, $Heap);
  var $rhs##0: Box
     where $IsBox($rhs##0, _module._default.Caller$G)
       && $IsAllocBox($rhs##0, _module._default.Caller$G, $Heap);
  var $rhs##1: Box
     where $IsBox($rhs##1, _module._default.Caller$G)
       && $IsAllocBox($rhs##1, _module._default.Caller$G, $Heap);
  var $rhs##2: Box
     where $IsBox($rhs##2, _module._default.Caller$G)
       && $IsAllocBox($rhs##2, _module._default.Caller$G, $Heap);
  var a##0: Box;

    // AddMethodImpl: Caller, Impl$$_module.__default.Caller
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(113,38): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(114,30)
    assume true;
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type G
    // TrCallStmt: Adding lhs with type G
    // TrCallStmt: Adding lhs with type G
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    a##0 := g#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1, $rhs##2 := Call$$_module.__default.Callee(_module._default.Caller$G, a##0);
    // TrCallStmt: After ProcessCallStmt
    a#0 := $rhs##0;
    b#0 := $rhs##1;
    c#0 := $rhs##2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(114,32)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(115,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(116,7)
        assume true;
        assume true;
        k#0 := a#0;
        defass#k#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(116,10)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(117,10)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(118,7)
            assume true;
            assume true;
            k#0 := b#0;
            defass#k#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(118,10)"} true;
        }
        else
        {
            // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(120,5)
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(120,5)
            assume true;
            assume true;
            k#0 := c#0;
            defass#k#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(120,12)"} true;
            assert defass#k#0;
            return;
        }
    }

    assert defass#k#0;
}



procedure CheckWellformed$$_module.__default.GM(_module._default.GM$G: Ty)
   returns (g#0: Box
       where $IsBox(g#0, _module._default.GM$G)
         && $IsAllocBox(g#0, _module._default.GM$G, $Heap));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.GM(_module._default.GM$G: Ty)
   returns (g#0: Box
       where $IsBox(g#0, _module._default.GM$G)
         && $IsAllocBox(g#0, _module._default.GM$G, $Heap));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.GM(_module._default.GM$G: Ty)
   returns (defass#g#0: bool, 
    g#0: Box
       where defass#g#0
         ==> $IsBox(g#0, _module._default.GM$G)
           && $IsAllocBox(g#0, _module._default.GM$G, $Heap), 
    $_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.GM(_module._default.GM$G: Ty)
   returns (defass#g#0: bool, g#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#a#0: bool;
  var a#0: Box
     where defass#a#0
       ==> $IsBox(a#0, _module._default.GM$G)
         && $IsAllocBox(a#0, _module._default.GM$G, $Heap);
  var defass#b#0: bool;
  var b#0: Box
     where defass#b#0
       ==> $IsBox(b#0, _module._default.GM$G)
         && $IsAllocBox(b#0, _module._default.GM$G, $Heap);

    // AddMethodImpl: GM, Impl$$_module.__default.GM
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(125,0): initial state"} true;
    $_reverifyPost := false;
    havoc a#0 /* where defass#a#0
       ==> $IsBox(a#0, _module._default.GM$G)
         && $IsAllocBox(a#0, _module._default.GM$G, $Heap) */, b#0 /* where defass#b#0
       ==> $IsBox(b#0, _module._default.GM$G)
         && $IsAllocBox(b#0, _module._default.GM$G, $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(127,5)
    assume true;
    assert defass#b#0;
    assume true;
    a#0 := b#0;
    defass#a#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(127,8)"} true;
    assert defass#g#0;
}



procedure CheckWellformed$$_module.__default.MM(_module._default.MM$G: Ty, 
    x#0: int, 
    g#0: Box
       where $IsBox(g#0, _module._default.MM$G)
         && $IsAllocBox(g#0, _module._default.MM$G, $Heap))
   returns (vv#0: Box
       where $IsBox(vv#0, _module._default.MM$G)
         && $IsAllocBox(vv#0, _module._default.MM$G, $Heap), 
    ww#0: Box
       where $IsBox(ww#0, _module._default.MM$G)
         && $IsAllocBox(ww#0, _module._default.MM$G, $Heap));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.MM(_module._default.MM$G: Ty, 
    x#0: int, 
    g#0: Box
       where $IsBox(g#0, _module._default.MM$G)
         && $IsAllocBox(g#0, _module._default.MM$G, $Heap))
   returns (vv#0: Box
       where $IsBox(vv#0, _module._default.MM$G)
         && $IsAllocBox(vv#0, _module._default.MM$G, $Heap), 
    ww#0: Box
       where $IsBox(ww#0, _module._default.MM$G)
         && $IsAllocBox(ww#0, _module._default.MM$G, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.MM(_module._default.MM$G: Ty, 
    x#0: int, 
    g#0: Box
       where $IsBox(g#0, _module._default.MM$G)
         && $IsAllocBox(g#0, _module._default.MM$G, $Heap))
   returns (defass#vv#0: bool, 
    vv#0: Box
       where defass#vv#0
         ==> $IsBox(vv#0, _module._default.MM$G)
           && $IsAllocBox(vv#0, _module._default.MM$G, $Heap), 
    defass#ww#0: bool, 
    ww#0: Box
       where defass#ww#0
         ==> $IsBox(ww#0, _module._default.MM$G)
           && $IsAllocBox(ww#0, _module._default.MM$G, $Heap), 
    $_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.MM(_module._default.MM$G: Ty, x#0: int, g#0: Box)
   returns (defass#vv#0: bool, vv#0: Box, defass#ww#0: bool, ww#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#a#0: bool;
  var a#0: Box
     where defass#a#0
       ==> $IsBox(a#0, _module._default.MM$G)
         && $IsAllocBox(a#0, _module._default.MM$G, $Heap);
  var defass#b#0: bool;
  var b#0: Box
     where defass#b#0
       ==> $IsBox(b#0, _module._default.MM$G)
         && $IsAllocBox(b#0, _module._default.MM$G, $Heap);
  var defass#c#0_0: bool;
  var c#0_0: Box
     where defass#c#0_0
       ==> $IsBox(c#0_0, _module._default.MM$G)
         && $IsAllocBox(c#0_0, _module._default.MM$G, $Heap);
  var v#0: Box
     where $IsBox(v#0, _module._default.MM$G)
       && $IsAllocBox(v#0, _module._default.MM$G, $Heap);
  var defass#w#0: bool;
  var w#0: Box
     where defass#w#0
       ==> $IsBox(w#0, _module._default.MM$G)
         && $IsAllocBox(w#0, _module._default.MM$G, $Heap);

    // AddMethodImpl: MM, Impl$$_module.__default.MM
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(131,0): initial state"} true;
    $_reverifyPost := false;
    havoc a#0 /* where defass#a#0
       ==> $IsBox(a#0, _module._default.MM$G)
         && $IsAllocBox(a#0, _module._default.MM$G, $Heap) */, b#0 /* where defass#b#0
       ==> $IsBox(b#0, _module._default.MM$G)
         && $IsAllocBox(b#0, _module._default.MM$G, $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(133,5)
    assume true;
    assert defass#b#0;
    assume true;
    a#0 := b#0;
    defass#a#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(133,8)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(134,3)
    assume true;
    if (x#0 < 10)
    {
        havoc c#0_0 /* where defass#c#0_0
           ==> $IsBox(c#0_0, _module._default.MM$G)
             && $IsAllocBox(c#0_0, _module._default.MM$G, $Heap) */;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(136,7)
        assume true;
        assert defass#c#0_0;
        assume true;
        a#0 := c#0_0;
        defass#a#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(136,10)"} true;
    }
    else
    {
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(138,12)
    assume true;
    assume true;
    v#0 := g#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(138,15)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(139,5)
    assume true;
    havoc v#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(139,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(140,6)
    assume true;
    assume true;
    vv#0 := v#0;
    defass#vv#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(140,9)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(141,12)
    assume true;
    havoc w#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(141,15)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(142,5)
    assume true;
    havoc w#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(142,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(143,6)
    assume true;
    assert defass#w#0;
    assume true;
    ww#0 := w#0;
    defass#ww#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(143,9)"} true;
    assert defass#vv#0;
    assert defass#ww#0;
}



procedure CheckWellformed$$_module.__default.Loop(_module._default.Loop$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.Loop$G)
         && $IsAllocBox(a#0, _module._default.Loop$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.Loop$G)
         && $IsAllocBox(b#0, _module._default.Loop$G, $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    k#0: int)
   returns (g#0: Box
       where $IsBox(g#0, _module._default.Loop$G)
         && $IsAllocBox(g#0, _module._default.Loop$G, $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Loop(_module._default.Loop$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.Loop$G)
         && $IsAllocBox(a#0, _module._default.Loop$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.Loop$G)
         && $IsAllocBox(b#0, _module._default.Loop$G, $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    k#0: int)
   returns (g#0: Box
       where $IsBox(g#0, _module._default.Loop$G)
         && $IsAllocBox(g#0, _module._default.Loop$G, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Loop(_module._default.Loop$G: Ty, 
    a#0: Box
       where $IsBox(a#0, _module._default.Loop$G)
         && $IsAllocBox(a#0, _module._default.Loop$G, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.Loop$G)
         && $IsAllocBox(b#0, _module._default.Loop$G, $Heap), 
    n#0: int where LitInt(0) <= n#0, 
    k#0: int)
   returns (defass#g#0: bool, 
    g#0: Box
       where defass#g#0
         ==> $IsBox(g#0, _module._default.Loop$G)
           && $IsAllocBox(g#0, _module._default.Loop$G, $Heap), 
    $_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Loop(_module._default.Loop$G: Ty, a#0: Box, b#0: Box, n#0: int, k#0: int)
   returns (defass#g#0: bool, g#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#w#0: bool;
  var w#0: Box
     where defass#w#0
       ==> $IsBox(w#0, _module._default.Loop$G)
         && $IsAllocBox(w#0, _module._default.Loop$G, $Heap);
  var defass#x#0: bool;
  var x#0: Box
     where defass#x#0
       ==> $IsBox(x#0, _module._default.Loop$G)
         && $IsAllocBox(x#0, _module._default.Loop$G, $Heap);
  var defass#y#0: bool;
  var y#0: Box
     where defass#y#0
       ==> $IsBox(y#0, _module._default.Loop$G)
         && $IsAllocBox(y#0, _module._default.Loop$G, $Heap);
  var defass#z#0: bool;
  var z#0: Box
     where defass#z#0
       ==> $IsBox(z#0, _module._default.Loop$G)
         && $IsAllocBox(z#0, _module._default.Loop$G, $Heap);
  var $rhs#0: Box where $IsBox($rhs#0, _module._default.Loop$G);
  var $rhs#1: Box where $IsBox($rhs#1, _module._default.Loop$G);
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var preLoop$loop#0$defass#g#0: bool;
  var preLoop$loop#0$defass#y#0: bool;
  var preLoop$loop#0$defass#x#0: bool;
  var preLoop$loop#0$defass#w#0: bool;
  var preLoop$loop#0$defass#z#0: bool;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $rhs#2_1_0: Box where $IsBox($rhs#2_1_0, _module._default.Loop$G);
  var $rhs#2_1_1: Box where $IsBox($rhs#2_1_1, _module._default.Loop$G);
  var lw#2_0: Box
     where $IsBox(lw#2_0, _module._default.Loop$G)
       && $IsAllocBox(lw#2_0, _module._default.Loop$G, $Heap);
  var lx#2_0: Box
     where $IsBox(lx#2_0, _module._default.Loop$G)
       && $IsAllocBox(lx#2_0, _module._default.Loop$G, $Heap);
  var defass#t#0: bool;
  var t#0: Box
     where defass#t#0
       ==> $IsBox(t#0, _module._default.Loop$G)
         && $IsAllocBox(t#0, _module._default.Loop$G, $Heap);
  var defass#t#1: bool;
  var t#1: Box
     where defass#t#1
       ==> $IsBox(t#1, _module._default.Loop$G)
         && $IsAllocBox(t#1, _module._default.Loop$G, $Heap);
  var $PreLoopHeap$loop#1: Heap;
  var preLoop$loop#1$defass#g#0: bool;
  var preLoop$loop#1$defass#y#0: bool;
  var preLoop$loop#1$defass#x#0: bool;
  var preLoop$loop#1$defass#w#0: bool;
  var preLoop$loop#1$defass#z#0: bool;
  var $decr_init$loop#10: int;
  var $w$loop#1: bool;
  var $decr$loop#10: int;

    // AddMethodImpl: Loop, Impl$$_module.__default.Loop
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(186,0): initial state"} true;
    $_reverifyPost := false;
    havoc w#0 /* where defass#w#0
       ==> $IsBox(w#0, _module._default.Loop$G)
         && $IsAllocBox(w#0, _module._default.Loop$G, $Heap) */, x#0 /* where defass#x#0
       ==> $IsBox(x#0, _module._default.Loop$G)
         && $IsAllocBox(x#0, _module._default.Loop$G, $Heap) */, y#0 /* where defass#y#0
       ==> $IsBox(y#0, _module._default.Loop$G)
         && $IsAllocBox(y#0, _module._default.Loop$G, $Heap) */, z#0 /* where defass#z#0
       ==> $IsBox(z#0, _module._default.Loop$G)
         && $IsAllocBox(z#0, _module._default.Loop$G, $Heap) */;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(188,8)
    assume true;
    assume true;
    assume true;
    $rhs#0 := a#0;
    assume true;
    $rhs#1 := a#0;
    w#0 := $rhs#0;
    defass#w#0 := true;
    x#0 := $rhs#1;
    defass#x#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(188,14)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(189,3)
    assume true;
    if (k#0 < 100)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(190,7)
        assume true;
        assume true;
        z#0 := a#0;
        defass#z#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(190,10)"} true;
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(192,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(192,12)
        assume true;
        assume true;
        y#0 := a#0;
        defass#y#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(192,15)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(192,29)
        assume true;
        assume true;
        y#0 := b#0;
        defass#y#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(192,32)"} true;
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(193,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(193,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(194,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#g#0 := defass#g#0;
    preLoop$loop#0$defass#y#0 := defass#y#0;
    preLoop$loop#0$defass#x#0 := defass#x#0;
    preLoop$loop#0$defass#w#0 := defass#w#0;
    preLoop$loop#0$defass#z#0 := defass#z#0;
    $decr_init$loop#00 := n#0 - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> 4 < i#0 ==> y#0 == a#0;
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> y#0 == b#0 || i#0 <= n#0;
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant preLoop$loop#0$defass#g#0 ==> defass#g#0;
      free invariant preLoop$loop#0$defass#y#0 ==> defass#y#0;
      free invariant preLoop$loop#0$defass#x#0 ==> defass#x#0;
      free invariant preLoop$loop#0$defass#w#0 ==> defass#w#0;
      free invariant preLoop$loop#0$defass#z#0 ==> defass#z#0;
      free invariant n#0 - i#0 <= $decr_init$loop#00 && (n#0 - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(194,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (4 < i#0)
            {
                assert defass#y#0;
            }

            assume true;
            assume 4 < i#0 ==> y#0 == a#0;
            assert defass#y#0;
            if (y#0 != b#0)
            {
            }

            assume true;
            assume y#0 == b#0 || i#0 <= n#0;
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#0)
        {
            break;
        }

        $decr$loop#00 := n#0 - i#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(198,5)
        assume true;
        if (i#0 == LitInt(4))
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(199,9)
            assume true;
            assume true;
            y#0 := a#0;
            defass#y#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(199,12)"} true;
        }
        else
        {
        }

        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(201,5)
        assert LitInt(2) != 0;
        assume true;
        if (Mod(i#0, LitInt(2)) == LitInt(0))
        {
            // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(202,12)
            assume true;
            assume true;
            assume true;
            $rhs#2_1_0 := b#0;
            assume true;
            $rhs#2_1_1 := b#0;
            x#0 := $rhs#2_1_0;
            defass#x#0 := true;
            z#0 := $rhs#2_1_1;
            defass#z#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(202,18)"} true;
        }
        else
        {
        }

        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(204,12)
        assume true;
        assert defass#w#0;
        assume true;
        lw#2_0 := w#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(204,15)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(205,12)
        assume true;
        assert defass#x#0;
        assume true;
        lx#2_0 := x#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(205,15)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(206,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(206,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(194,3)
        assert 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert n#0 - i#0 < $decr$loop#00;
        assume true;
        assume true;
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(208,5)
    assume true;
    assert defass#w#0;
    assume true;
    g#0 := w#0;
    defass#g#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(208,8)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(209,5)
    assume true;
    assert defass#x#0;
    assume true;
    g#0 := x#0;
    defass#g#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(209,8)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(210,3)
    assume true;
    if (k#0 < 100)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(211,7)
        assume true;
        assert defass#z#0;
        assume true;
        g#0 := z#0;
        defass#g#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(211,10)"} true;
    }
    else
    {
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(213,5)
    assume true;
    havoc g#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(213,8)"} true;
    havoc t#0 /* where defass#t#0
       ==> $IsBox(t#0, _module._default.Loop$G)
         && $IsAllocBox(t#0, _module._default.Loop$G, $Heap) */;
    havoc t#1 /* where defass#t#1
       ==> $IsBox(t#1, _module._default.Loop$G)
         && $IsAllocBox(t#1, _module._default.Loop$G, $Heap) */;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(217,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#1 := $Heap;
    preLoop$loop#1$defass#g#0 := defass#g#0;
    preLoop$loop#1$defass#y#0 := defass#y#0;
    preLoop$loop#1$defass#x#0 := defass#x#0;
    preLoop$loop#1$defass#w#0 := defass#w#0;
    preLoop$loop#1$defass#z#0 := defass#z#0;
    $decr_init$loop#10 := i#0 - 0;
    havoc $w$loop#1;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#1[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#1, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#1, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1, $o, $f) || $_Frame[$o, $f]);
      free invariant preLoop$loop#1$defass#g#0 ==> defass#g#0;
      free invariant preLoop$loop#1$defass#y#0 ==> defass#y#0;
      free invariant preLoop$loop#1$defass#x#0 ==> defass#x#0;
      free invariant preLoop$loop#1$defass#w#0 ==> defass#w#0;
      free invariant preLoop$loop#1$defass#z#0 ==> defass#z#0;
      free invariant i#0 - 0 <= $decr_init$loop#10 && (i#0 - 0 == $decr_init$loop#10 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(217,2): after some loop iterations"} true;
        if (!$w$loop#1)
        {
            assume true;
            assume false;
        }

        assume true;
        if (i#0 <= 0)
        {
            break;
        }

        $decr$loop#10 := i#0 - 0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(218,7)
        assume true;
        assume true;
        i#0 := i#0 - 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(218,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(217,3)
        assert 0 <= $decr$loop#10 || i#0 - 0 == $decr$loop#10;
        assert i#0 - 0 < $decr$loop#10;
    }

    assert defass#g#0;
}



// function declaration for _module._default.Two
function _module.__default.Two(_module._default.Two$T: Ty, t#0: Box) : DatatypeType;

function _module.__default.Two#canCall(_module._default.Two$T: Ty, t#0: Box) : bool;

// consequence axiom for _module.__default.Two
axiom 6 <= $FunctionContextHeight
   ==> (forall _module._default.Two$T: Ty, t#0: Box :: 
    { _module.__default.Two(_module._default.Two$T, t#0) } 
    _module.__default.Two#canCall(_module._default.Two$T, t#0)
         || (6 != $FunctionContextHeight && $IsBox(t#0, _module._default.Two$T))
       ==> $Is(_module.__default.Two(_module._default.Two$T, t#0), 
        Tclass._System.Tuple2(_module._default.Two$T, _module._default.Two$T)));

function _module.__default.Two#requires(Ty, Box) : bool;

// #requires axiom for _module.__default.Two
axiom (forall _module._default.Two$T: Ty, t#0: Box :: 
  { _module.__default.Two#requires(_module._default.Two$T, t#0) } 
  $IsBox(t#0, _module._default.Two$T)
     ==> _module.__default.Two#requires(_module._default.Two$T, t#0) == true);

// definition axiom for _module.__default.Two (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall _module._default.Two$T: Ty, t#0: Box :: 
    { _module.__default.Two(_module._default.Two$T, t#0) } 
    _module.__default.Two#canCall(_module._default.Two$T, t#0)
         || (6 != $FunctionContextHeight && $IsBox(t#0, _module._default.Two$T))
       ==> _module.__default.Two(_module._default.Two$T, t#0)
         == #_System._tuple#2._#Make2(t#0, t#0));

// definition axiom for _module.__default.Two for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall _module._default.Two$T: Ty, t#0: Box :: 
    {:weight 3} { _module.__default.Two(_module._default.Two$T, Lit(t#0)) } 
    _module.__default.Two#canCall(_module._default.Two$T, Lit(t#0))
         || (6 != $FunctionContextHeight && $IsBox(t#0, _module._default.Two$T))
       ==> _module.__default.Two(_module._default.Two$T, Lit(t#0))
         == Lit(#_System._tuple#2._#Make2(Lit(t#0), Lit(t#0))));

procedure CheckWellformed$$_module.__default.Two(_module._default.Two$T: Ty, t#0: Box where $IsBox(t#0, _module._default.Two$T));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.TwoMethod(_module._default.TwoMethod$T: Ty, 
    t#0: Box
       where $IsBox(t#0, _module._default.TwoMethod$T)
         && $IsAllocBox(t#0, _module._default.TwoMethod$T, $Heap))
   returns (a#0: Box
       where $IsBox(a#0, _module._default.TwoMethod$T)
         && $IsAllocBox(a#0, _module._default.TwoMethod$T, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.TwoMethod$T)
         && $IsAllocBox(b#0, _module._default.TwoMethod$T, $Heap));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TwoMethod(_module._default.TwoMethod$T: Ty, 
    t#0: Box
       where $IsBox(t#0, _module._default.TwoMethod$T)
         && $IsAllocBox(t#0, _module._default.TwoMethod$T, $Heap))
   returns (a#0: Box
       where $IsBox(a#0, _module._default.TwoMethod$T)
         && $IsAllocBox(a#0, _module._default.TwoMethod$T, $Heap), 
    b#0: Box
       where $IsBox(b#0, _module._default.TwoMethod$T)
         && $IsAllocBox(b#0, _module._default.TwoMethod$T, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TwoMethod(_module._default.TwoMethod$T: Ty, 
    t#0: Box
       where $IsBox(t#0, _module._default.TwoMethod$T)
         && $IsAllocBox(t#0, _module._default.TwoMethod$T, $Heap))
   returns (defass#a#0: bool, 
    a#0: Box
       where defass#a#0
         ==> $IsBox(a#0, _module._default.TwoMethod$T)
           && $IsAllocBox(a#0, _module._default.TwoMethod$T, $Heap), 
    defass#b#0: bool, 
    b#0: Box
       where defass#b#0
         ==> $IsBox(b#0, _module._default.TwoMethod$T)
           && $IsAllocBox(b#0, _module._default.TwoMethod$T, $Heap), 
    $_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TwoMethod(_module._default.TwoMethod$T: Ty, t#0: Box)
   returns (defass#a#0: bool, a#0: Box, defass#b#0: bool, b#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Box where $IsBox($rhs#0, _module._default.TwoMethod$T);
  var $rhs#1: Box where $IsBox($rhs#1, _module._default.TwoMethod$T);

    // AddMethodImpl: TwoMethod, Impl$$_module.__default.TwoMethod
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(230,0): initial state"} true;
    $_reverifyPost := false;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(231,8)
    assume true;
    assume true;
    assume true;
    $rhs#0 := t#0;
    assume true;
    $rhs#1 := t#0;
    a#0 := $rhs#0;
    defass#a#0 := true;
    b#0 := $rhs#1;
    defass#b#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(231,14)"} true;
    assert defass#a#0;
    assert defass#b#0;
}



procedure CheckWellformed$$_module.__default.UnderscoresAndPatterns0(_module._default.UnderscoresAndPatterns0$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns0$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns0$T, $Heap));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UnderscoresAndPatterns0(_module._default.UnderscoresAndPatterns0$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns0$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns0$T, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UnderscoresAndPatterns0(_module._default.UnderscoresAndPatterns0$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns0$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns0$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UnderscoresAndPatterns0(_module._default.UnderscoresAndPatterns0$T: Ty, tt#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#a#0: bool;
  var a#0: Box
     where defass#a#0
       ==> $IsBox(a#0, _module._default.UnderscoresAndPatterns0$T)
         && $IsAllocBox(a#0, _module._default.UnderscoresAndPatterns0$T, $Heap);
  var defass#b#0: bool;
  var b#0: Box
     where defass#b#0
       ==> $IsBox(b#0, _module._default.UnderscoresAndPatterns0$T)
         && $IsAllocBox(b#0, _module._default.UnderscoresAndPatterns0$T, $Heap);
  var a'#0: Box
     where $IsBox(a'#0, _module._default.UnderscoresAndPatterns0$T)
       && $IsAllocBox(a'#0, _module._default.UnderscoresAndPatterns0$T, $Heap);
  var b'#0: Box
     where $IsBox(b'#0, _module._default.UnderscoresAndPatterns0$T)
       && $IsAllocBox(b'#0, _module._default.UnderscoresAndPatterns0$T, $Heap);

    // AddMethodImpl: UnderscoresAndPatterns0, Impl$$_module.__default.UnderscoresAndPatterns0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(235,0): initial state"} true;
    $_reverifyPost := false;
    havoc a#0 /* where defass#a#0
       ==> $IsBox(a#0, _module._default.UnderscoresAndPatterns0$T)
         && $IsAllocBox(a#0, _module._default.UnderscoresAndPatterns0$T, $Heap) */, b#0 /* where defass#b#0
       ==> $IsBox(b#0, _module._default.UnderscoresAndPatterns0$T)
         && $IsAllocBox(b#0, _module._default.UnderscoresAndPatterns0$T, $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(237,10)
    assume true;
    assert defass#a#0;
    assume true;
    a'#0 := a#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(237,13)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(238,10)
    assume true;
    assert defass#b#0;
    assume true;
    b'#0 := b#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(238,13)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(239,3)
    assume true;
    assume true;
    assume true;
    assume true;
}



procedure CheckWellformed$$_module.__default.UnderscoresAndPatterns1(_module._default.UnderscoresAndPatterns1$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns1$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns1$T, $Heap));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UnderscoresAndPatterns1(_module._default.UnderscoresAndPatterns1$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns1$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns1$T, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UnderscoresAndPatterns1(_module._default.UnderscoresAndPatterns1$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns1$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns1$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.UnderscoresAndPatterns2(_module._default.UnderscoresAndPatterns2$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns2$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns2$T, $Heap));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UnderscoresAndPatterns2(_module._default.UnderscoresAndPatterns2$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns2$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns2$T, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UnderscoresAndPatterns2(_module._default.UnderscoresAndPatterns2$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns2$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns2$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.UnderscoresAndPatterns3(_module._default.UnderscoresAndPatterns3$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns3$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns3$T, $Heap));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.UnderscoresAndPatterns3(_module._default.UnderscoresAndPatterns3$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns3$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns3$T, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.UnderscoresAndPatterns3(_module._default.UnderscoresAndPatterns3$T: Ty, 
    tt#0: Box
       where $IsBox(tt#0, _module._default.UnderscoresAndPatterns3$T)
         && $IsAllocBox(tt#0, _module._default.UnderscoresAndPatterns3$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.UnderscoresAndPatterns3(_module._default.UnderscoresAndPatterns3$T: Ty, tt#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _v1#0: Box
     where $IsBox(_v1#0, _module._default.UnderscoresAndPatterns3$T)
       && $IsAllocBox(_v1#0, _module._default.UnderscoresAndPatterns3$T, $Heap);
  var b#0: Box
     where $IsBox(b#0, _module._default.UnderscoresAndPatterns3$T)
       && $IsAllocBox(b#0, _module._default.UnderscoresAndPatterns3$T, $Heap);
  var $rhs##0: Box
     where $IsBox($rhs##0, _module._default.UnderscoresAndPatterns3$T)
       && $IsAllocBox($rhs##0, _module._default.UnderscoresAndPatterns3$T, $Heap);
  var $rhs##1: Box
     where $IsBox($rhs##1, _module._default.UnderscoresAndPatterns3$T)
       && $IsAllocBox($rhs##1, _module._default.UnderscoresAndPatterns3$T, $Heap);
  var t##0: Box;
  var b'#0: Box
     where $IsBox(b'#0, _module._default.UnderscoresAndPatterns3$T)
       && $IsAllocBox(b'#0, _module._default.UnderscoresAndPatterns3$T, $Heap);

    // AddMethodImpl: UnderscoresAndPatterns3, Impl$$_module.__default.UnderscoresAndPatterns3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(259,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(260,27)
    assume true;
    assume true;
    // TrCallStmt: Adding lhs with type T
    // TrCallStmt: Adding lhs with type T
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    t##0 := tt#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0, $rhs##1 := Call$$_module.__default.TwoMethod(_module._default.UnderscoresAndPatterns3$T, t##0);
    // TrCallStmt: After ProcessCallStmt
    _v1#0 := $rhs##0;
    b#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(260,30)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(261,10)
    assume true;
    assume true;
    b'#0 := b#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/DefiniteAssignment.dfy(261,13)"} true;
}



const #$D: Ty;

const unique class.AssignSuchThat.D: ClassName;

const unique class.AssignSuchThat.__default: ClassName;

function Tclass.AssignSuchThat.__default() : Ty;

const unique Tagclass.AssignSuchThat.__default: TyTag;

// Tclass.AssignSuchThat.__default Tag
axiom Tag(Tclass.AssignSuchThat.__default()) == Tagclass.AssignSuchThat.__default
   && TagFamily(Tclass.AssignSuchThat.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.AssignSuchThat.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AssignSuchThat.__default()) } 
  $IsBox(bx, Tclass.AssignSuchThat.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AssignSuchThat.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.AssignSuchThat.__default()) } 
  $Is($o, Tclass.AssignSuchThat.__default())
     <==> $o == null || dtype($o) == Tclass.AssignSuchThat.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.AssignSuchThat.__default(), $h) } 
  $IsAlloc($o, Tclass.AssignSuchThat.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.AssignSuchThatReference.D?: ClassName;

function Tclass.AssignSuchThatReference.D?() : Ty;

const unique Tagclass.AssignSuchThatReference.D?: TyTag;

// Tclass.AssignSuchThatReference.D? Tag
axiom Tag(Tclass.AssignSuchThatReference.D?()) == Tagclass.AssignSuchThatReference.D?
   && TagFamily(Tclass.AssignSuchThatReference.D?()) == tytagFamily$D;

// Box/unbox axiom for Tclass.AssignSuchThatReference.D?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AssignSuchThatReference.D?()) } 
  $IsBox(bx, Tclass.AssignSuchThatReference.D?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AssignSuchThatReference.D?()));

// D: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.AssignSuchThatReference.D?()) } 
  $Is($o, Tclass.AssignSuchThatReference.D?())
     <==> $o == null || implements$AssignSuchThatReference.D(dtype($o)));

// D: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.AssignSuchThatReference.D?(), $h) } 
  $IsAlloc($o, Tclass.AssignSuchThatReference.D?(), $h)
     <==> $o == null || read($h, $o, alloc));

function implements$AssignSuchThatReference.D(Ty) : bool;

function AssignSuchThatReference.D.x(this: ref) : int;

// D.x: Type axiom
axiom (forall $o: ref :: 
  { AssignSuchThatReference.D.x($o) } 
  $Is(AssignSuchThatReference.D.x($o), TInt));

// D.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { AssignSuchThatReference.D.x($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(AssignSuchThatReference.D.x($o), TInt, $h));

function Tclass.AssignSuchThatReference.D() : Ty;

const unique Tagclass.AssignSuchThatReference.D: TyTag;

// Tclass.AssignSuchThatReference.D Tag
axiom Tag(Tclass.AssignSuchThatReference.D()) == Tagclass.AssignSuchThatReference.D
   && TagFamily(Tclass.AssignSuchThatReference.D()) == tytagFamily$D;

// Box/unbox axiom for Tclass.AssignSuchThatReference.D
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AssignSuchThatReference.D()) } 
  $IsBox(bx, Tclass.AssignSuchThatReference.D())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AssignSuchThatReference.D()));

// AssignSuchThatReference.D: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.AssignSuchThatReference.D()) } 
  $Is(c#0, Tclass.AssignSuchThatReference.D())
     <==> $Is(c#0, Tclass.AssignSuchThatReference.D?()) && c#0 != null);

// AssignSuchThatReference.D: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.AssignSuchThatReference.D(), $h) } 
  $IsAlloc(c#0, Tclass.AssignSuchThatReference.D(), $h)
     <==> $IsAlloc(c#0, Tclass.AssignSuchThatReference.D?(), $h));

const unique class.AssignSuchThatReference.__default: ClassName;

function Tclass.AssignSuchThatReference.__default() : Ty;

const unique Tagclass.AssignSuchThatReference.__default: TyTag;

// Tclass.AssignSuchThatReference.__default Tag
axiom Tag(Tclass.AssignSuchThatReference.__default())
     == Tagclass.AssignSuchThatReference.__default
   && TagFamily(Tclass.AssignSuchThatReference.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.AssignSuchThatReference.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AssignSuchThatReference.__default()) } 
  $IsBox(bx, Tclass.AssignSuchThatReference.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AssignSuchThatReference.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.AssignSuchThatReference.__default()) } 
  $Is($o, Tclass.AssignSuchThatReference.__default())
     <==> $o == null || dtype($o) == Tclass.AssignSuchThatReference.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.AssignSuchThatReference.__default(), $h) } 
  $IsAlloc($o, Tclass.AssignSuchThatReference.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const #$C: Ty;

const unique class.LetSuchThat.C: ClassName;

const unique class.LetSuchThat.__default: ClassName;

function Tclass.LetSuchThat.__default() : Ty;

const unique Tagclass.LetSuchThat.__default: TyTag;

// Tclass.LetSuchThat.__default Tag
axiom Tag(Tclass.LetSuchThat.__default()) == Tagclass.LetSuchThat.__default
   && TagFamily(Tclass.LetSuchThat.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.LetSuchThat.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.LetSuchThat.__default()) } 
  $IsBox(bx, Tclass.LetSuchThat.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.LetSuchThat.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.LetSuchThat.__default()) } 
  $Is($o, Tclass.LetSuchThat.__default())
     <==> $o == null || dtype($o) == Tclass.LetSuchThat.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.LetSuchThat.__default(), $h) } 
  $IsAlloc($o, Tclass.LetSuchThat.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for LetSuchThat._default.Bad
function LetSuchThat.__default.Bad() : int;

function LetSuchThat.__default.Bad#canCall() : bool;

// consequence axiom for LetSuchThat.__default.Bad
axiom true ==> true ==> true;

function LetSuchThat.__default.Bad#requires() : bool;

// #requires axiom for LetSuchThat.__default.Bad
axiom (forall $Heap: Heap :: 
  { LetSuchThat.__default.Bad#requires(), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) ==> LetSuchThat.__default.Bad#requires() == true);

function $let#0_c() : Box;

function $let#0$canCall() : bool;

axiom $let#0$canCall() ==> Lit(true);

// definition axiom for LetSuchThat.__default.Bad (revealed)
axiom true
   ==> (forall $Heap: Heap :: 
    { LetSuchThat.__default.Bad(), $IsGoodHeap($Heap) } 
    LetSuchThat.__default.Bad#canCall() || $IsGoodHeap($Heap)
       ==> $let#0$canCall()
         && LetSuchThat.__default.Bad() == (var c#0 := $let#0_c(); LitInt(5)));

// definition axiom for LetSuchThat.__default.Bad for all literals (revealed)
axiom true
   ==> (forall $Heap: Heap :: 
    {:weight 3} { LetSuchThat.__default.Bad(), $IsGoodHeap($Heap) } 
    LetSuchThat.__default.Bad#canCall() || $IsGoodHeap($Heap)
       ==> $let#0$canCall()
         && LetSuchThat.__default.Bad() == (var c#0 := $let#0_c(); LitInt(5)));

// function declaration for LetSuchThat._default.Good
function LetSuchThat.__default.Good(y#0: Box) : int;

function LetSuchThat.__default.Good#canCall(y#0: Box) : bool;

// consequence axiom for LetSuchThat.__default.Good
axiom true
   ==> (forall y#0: Box :: 
    { LetSuchThat.__default.Good(y#0) } 
    LetSuchThat.__default.Good#canCall(y#0) || $IsBox(y#0, #$C) ==> true);

function LetSuchThat.__default.Good#requires(Box) : bool;

// #requires axiom for LetSuchThat.__default.Good
axiom (forall $Heap: Heap, y#0: Box :: 
  { LetSuchThat.__default.Good#requires(y#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $IsBox(y#0, #$C)
     ==> LetSuchThat.__default.Good#requires(y#0) == true);

function $let#1_c() : Box;

function $let#1$canCall() : bool;

axiom $let#1$canCall() ==> Lit(true);

// definition axiom for LetSuchThat.__default.Good (revealed)
axiom true
   ==> (forall $Heap: Heap, y#0: Box :: 
    { LetSuchThat.__default.Good(y#0), $IsGoodHeap($Heap) } 
    LetSuchThat.__default.Good#canCall(y#0)
         || ($IsGoodHeap($Heap) && $IsBox(y#0, #$C))
       ==> $let#1$canCall()
         && LetSuchThat.__default.Good(y#0) == (var c#0 := $let#1_c(); LitInt(5)));

// definition axiom for LetSuchThat.__default.Good for all literals (revealed)
axiom true
   ==> (forall $Heap: Heap, y#0: Box :: 
    {:weight 3} { LetSuchThat.__default.Good(Lit(y#0)), $IsGoodHeap($Heap) } 
    LetSuchThat.__default.Good#canCall(Lit(y#0))
         || ($IsGoodHeap($Heap) && $IsBox(y#0, #$C))
       ==> $let#1$canCall()
         && LetSuchThat.__default.Good(Lit(y#0)) == (var c#0 := $let#1_c(); LitInt(5)));

const unique class.NonEmpty.MyClass?: ClassName;

function Tclass.NonEmpty.MyClass?(Ty) : Ty;

const unique Tagclass.NonEmpty.MyClass?: TyTag;

// Tclass.NonEmpty.MyClass? Tag
axiom (forall NonEmpty.MyClass$G: Ty :: 
  { Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G) } 
  Tag(Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)) == Tagclass.NonEmpty.MyClass?
     && TagFamily(Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)) == tytagFamily$MyClass);

// Tclass.NonEmpty.MyClass? injectivity 0
axiom (forall NonEmpty.MyClass$G: Ty :: 
  { Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G) } 
  Tclass.NonEmpty.MyClass?_0(Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G))
     == NonEmpty.MyClass$G);

function Tclass.NonEmpty.MyClass?_0(Ty) : Ty;

// Box/unbox axiom for Tclass.NonEmpty.MyClass?
axiom (forall NonEmpty.MyClass$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)) } 
  $IsBox(bx, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)));

// MyClass: Class $Is
axiom (forall NonEmpty.MyClass$G: Ty, $o: ref :: 
  { $Is($o, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)) } 
  $Is($o, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G))
     <==> $o == null || dtype($o) == Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G));

// MyClass: Class $IsAlloc
axiom (forall NonEmpty.MyClass$G: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G), $h) } 
  $IsAlloc($o, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G), $h)
     <==> $o == null || read($h, $o, alloc));

function NonEmpty.MyClass.x(NonEmpty.MyClass$G: Ty, this: ref) : Box;

// MyClass.x: Type axiom
axiom (forall NonEmpty.MyClass$G: Ty, $o: ref :: 
  { NonEmpty.MyClass.x(NonEmpty.MyClass$G, $o) } 
  $IsBox(NonEmpty.MyClass.x(NonEmpty.MyClass$G, $o), NonEmpty.MyClass$G));

// MyClass.x: Allocation axiom
axiom (forall NonEmpty.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { NonEmpty.MyClass.x(NonEmpty.MyClass$G, $o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAllocBox(NonEmpty.MyClass.x(NonEmpty.MyClass$G, $o), NonEmpty.MyClass$G, $h));

axiom FDim(NonEmpty.MyClass.y) == 0
   && FieldOfDecl(class.NonEmpty.MyClass?, field$y) == NonEmpty.MyClass.y
   && !$IsGhostField(NonEmpty.MyClass.y);

const NonEmpty.MyClass.y: Field Box;

// MyClass.y: Type axiom
axiom (forall NonEmpty.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, NonEmpty.MyClass.y), Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)
     ==> $IsBox(read($h, $o, NonEmpty.MyClass.y), NonEmpty.MyClass$G));

// MyClass.y: Allocation axiom
axiom (forall NonEmpty.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, NonEmpty.MyClass.y), Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, NonEmpty.MyClass.y), NonEmpty.MyClass$G, $h));

axiom FDim(NonEmpty.MyClass.oxA) == 0
   && FieldOfDecl(class.NonEmpty.MyClass?, field$oxA) == NonEmpty.MyClass.oxA
   && $IsGhostField(NonEmpty.MyClass.oxA);

const NonEmpty.MyClass.oxA: Field Box;

// MyClass.oxA: Type axiom
axiom (forall NonEmpty.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, NonEmpty.MyClass.oxA), Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)
     ==> $IsBox(read($h, $o, NonEmpty.MyClass.oxA), NonEmpty.MyClass$G));

// MyClass.oxA: Allocation axiom
axiom (forall NonEmpty.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, NonEmpty.MyClass.oxA), Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, NonEmpty.MyClass.oxA), NonEmpty.MyClass$G, $h));

function NonEmpty.MyClass.oxB(NonEmpty.MyClass$G: Ty, this: ref) : Box;

// MyClass.oxB: Type axiom
axiom (forall NonEmpty.MyClass$G: Ty, $o: ref :: 
  { NonEmpty.MyClass.oxB(NonEmpty.MyClass$G, $o) } 
  $IsBox(NonEmpty.MyClass.oxB(NonEmpty.MyClass$G, $o), NonEmpty.MyClass$G));

// MyClass.oxB: Allocation axiom
axiom (forall NonEmpty.MyClass$G: Ty, $h: Heap, $o: ref :: 
  { NonEmpty.MyClass.oxB(NonEmpty.MyClass$G, $o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAllocBox(NonEmpty.MyClass.oxB(NonEmpty.MyClass$G, $o), NonEmpty.MyClass$G, $h));

function Tclass.NonEmpty.MyClass(Ty) : Ty;

const unique Tagclass.NonEmpty.MyClass: TyTag;

// Tclass.NonEmpty.MyClass Tag
axiom (forall NonEmpty.MyClass$G: Ty :: 
  { Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G) } 
  Tag(Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G)) == Tagclass.NonEmpty.MyClass
     && TagFamily(Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G)) == tytagFamily$MyClass);

// Tclass.NonEmpty.MyClass injectivity 0
axiom (forall NonEmpty.MyClass$G: Ty :: 
  { Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G) } 
  Tclass.NonEmpty.MyClass_0(Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G))
     == NonEmpty.MyClass$G);

function Tclass.NonEmpty.MyClass_0(Ty) : Ty;

// Box/unbox axiom for Tclass.NonEmpty.MyClass
axiom (forall NonEmpty.MyClass$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G)) } 
  $IsBox(bx, Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G)));

// NonEmpty.MyClass: subset type $Is
axiom (forall NonEmpty.MyClass$G: Ty, c#0: ref :: 
  { $Is(c#0, Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G)) } 
  $Is(c#0, Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G))
     <==> $Is(c#0, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G)) && c#0 != null);

// NonEmpty.MyClass: subset type $IsAlloc
axiom (forall NonEmpty.MyClass$G: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G), $h) } 
  $IsAlloc(c#0, Tclass.NonEmpty.MyClass(NonEmpty.MyClass$G), $h)
     <==> $IsAlloc(c#0, Tclass.NonEmpty.MyClass?(NonEmpty.MyClass$G), $h));

const unique class.NonEmpty.__default: ClassName;

function Tclass.NonEmpty.__default() : Ty;

const unique Tagclass.NonEmpty.__default: TyTag;

// Tclass.NonEmpty.__default Tag
axiom Tag(Tclass.NonEmpty.__default()) == Tagclass.NonEmpty.__default
   && TagFamily(Tclass.NonEmpty.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.NonEmpty.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.NonEmpty.__default()) } 
  $IsBox(bx, Tclass.NonEmpty.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.NonEmpty.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.NonEmpty.__default()) } 
  $Is($o, Tclass.NonEmpty.__default())
     <==> $o == null || dtype($o) == Tclass.NonEmpty.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.NonEmpty.__default(), $h) } 
  $IsAlloc($o, Tclass.NonEmpty.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

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

const unique tytagFamily$MyClass: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$NonNullC: TyTagFamily;

const unique tytagFamily$Iter: TyTagFamily;

const unique tytagFamily$Regression213: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$D: TyTagFamily;

const unique field$y: NameFamily;

const unique field$oxA: NameFamily;

const unique field$u: NameFamily;

const unique field$ug: NameFamily;

const unique field$z: NameFamily;

const unique field$ys: NameFamily;

const unique field$ugs: NameFamily;

const unique field$zs: NameFamily;

const unique field$_new: NameFamily;
