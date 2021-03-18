// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy -print:./SmallTests.bpl

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

const unique class._module.Node?: ClassName;

function Tclass._module.Node?() : Ty;

const unique Tagclass._module.Node?: TyTag;

// Tclass._module.Node? Tag
axiom Tag(Tclass._module.Node?()) == Tagclass._module.Node?
   && TagFamily(Tclass._module.Node?()) == tytagFamily$Node;

// Box/unbox axiom for Tclass._module.Node?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Node?()) } 
  $IsBox(bx, Tclass._module.Node?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Node?()));

// Node: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Node?()) } 
  $Is($o, Tclass._module.Node?())
     <==> $o == null || dtype($o) == Tclass._module.Node?());

// Node: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Node?(), $h) } 
  $IsAlloc($o, Tclass._module.Node?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Node.next) == 0
   && FieldOfDecl(class._module.Node?, field$next) == _module.Node.next
   && !$IsGhostField(_module.Node.next);

const _module.Node.next: Field ref;

// Node.next: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.next) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Node?()
     ==> $Is(read($h, $o, _module.Node.next), Tclass._module.Node?()));

// Node.next: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Node.next) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Node.next), Tclass._module.Node?(), $h));

// function declaration for _module.Node.IsList
function _module.Node.IsList($ly: LayerType, $heap: Heap, this: ref, r#0: Set Box) : bool;

function _module.Node.IsList#canCall($heap: Heap, this: ref, r#0: Set Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, r#0: Set Box :: 
  { _module.Node.IsList($LS($ly), $Heap, this, r#0) } 
  _module.Node.IsList($LS($ly), $Heap, this, r#0)
     == _module.Node.IsList($ly, $Heap, this, r#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, r#0: Set Box :: 
  { _module.Node.IsList(AsFuelBottom($ly), $Heap, this, r#0) } 
  _module.Node.IsList($ly, $Heap, this, r#0)
     == _module.Node.IsList($LZ, $Heap, this, r#0));

function Tclass._module.Node() : Ty;

const unique Tagclass._module.Node: TyTag;

// Tclass._module.Node Tag
axiom Tag(Tclass._module.Node()) == Tagclass._module.Node
   && TagFamily(Tclass._module.Node()) == tytagFamily$Node;

// Box/unbox axiom for Tclass._module.Node
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Node()) } 
  $IsBox(bx, Tclass._module.Node())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Node()));

// frame axiom for _module.Node.IsList
axiom (forall $ly: LayerType, $h0: Heap, $h1: Heap, this: ref, r#0: Set Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.IsList($ly, $h1, this, r#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && (_module.Node.IsList#canCall($h0, this, r#0)
         || $Is(r#0, TSet(Tclass._module.Node())))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && r#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.IsList($ly, $h0, this, r#0)
       == _module.Node.IsList($ly, $h1, this, r#0));

// consequence axiom for _module.Node.IsList
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, r#0: Set Box :: 
    { _module.Node.IsList($ly, $Heap, this, r#0) } 
    _module.Node.IsList#canCall($Heap, this, r#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap)
           && $Is(r#0, TSet(Tclass._module.Node())))
       ==> true);

function _module.Node.IsList#requires(LayerType, Heap, ref, Set Box) : bool;

// #requires axiom for _module.Node.IsList
axiom (forall $ly: LayerType, $Heap: Heap, this: ref, r#0: Set Box :: 
  { _module.Node.IsList#requires($ly, $Heap, this, r#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
       && $Is(r#0, TSet(Tclass._module.Node()))
     ==> _module.Node.IsList#requires($ly, $Heap, this, r#0) == true);

// definition axiom for _module.Node.IsList (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref, r#0: Set Box :: 
    { _module.Node.IsList($LS($ly), $Heap, this, r#0), $IsGoodHeap($Heap) } 
    _module.Node.IsList#canCall($Heap, this, r#0)
         || (1 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap)
           && $Is(r#0, TSet(Tclass._module.Node())))
       ==> (r#0[$Box(this)]
           ==> 
          read($Heap, this, _module.Node.next) != null
           ==> _module.Node.IsList#canCall($Heap, 
            read($Heap, this, _module.Node.next), 
            Set#Difference(r#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))))
         && _module.Node.IsList($LS($ly), $Heap, this, r#0)
           == (r#0[$Box(this)]
             && (read($Heap, this, _module.Node.next) != null
               ==> _module.Node.IsList($ly, 
                $Heap, 
                read($Heap, this, _module.Node.next), 
                Set#Difference(r#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)))))));

procedure CheckWellformed$$_module.Node.IsList(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    r#0: Set Box where $Is(r#0, TSet(Tclass._module.Node())));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.IsList(this: ref, r#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##r#0: Set Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function IsList
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(8,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> r#0[$Box($o)]);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> r#0[$Box($o)]);
        if (r#0[$Box(this)])
        {
            b$reqreads#0 := $_Frame[this, _module.Node.next];
            if (read($Heap, this, _module.Node.next) != null)
            {
                b$reqreads#1 := $_Frame[this, _module.Node.next];
                assert read($Heap, this, _module.Node.next) != null;
                ##r#0 := Set#Difference(r#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#0, TSet(Tclass._module.Node()), $Heap);
                b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null && read($Heap, $o, alloc) && ##r#0[$Box($o)] ==> $_Frame[$o, $f]);
                assert (Set#Subset(##r#0, r#0) && !Set#Subset(r#0, ##r#0))
                   || (Set#Equal(##r#0, r#0) && Set#Subset(##r#0, r#0) && !Set#Subset(r#0, ##r#0));
                assume _module.Node.IsList#canCall($Heap, 
                  read($Heap, this, _module.Node.next), 
                  Set#Difference(r#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this))));
            }
        }

        assume _module.Node.IsList($LS($LZ), $Heap, this, r#0)
           == (r#0[$Box(this)]
             && (read($Heap, this, _module.Node.next) != null
               ==> _module.Node.IsList($LS($LZ), 
                $Heap, 
                read($Heap, this, _module.Node.next), 
                Set#Difference(r#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this))))));
        assume r#0[$Box(this)]
           ==> 
          read($Heap, this, _module.Node.next) != null
           ==> _module.Node.IsList#canCall($Heap, 
            read($Heap, this, _module.Node.next), 
            Set#Difference(r#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.IsList($LS($LZ), $Heap, this, r#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



procedure CheckWellformed$$_module.Node.Test(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    n#0: ref
       where $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap), 
    nodes#0: Set Box
       where $Is(nodes#0, TSet(Tclass._module.Node()))
         && $IsAlloc(nodes#0, TSet(Tclass._module.Node()), $Heap));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.Test(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    n#0: ref
       where $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap), 
    nodes#0: Set Box
       where $Is(nodes#0, TSet(Tclass._module.Node()))
         && $IsAlloc(nodes#0, TSet(Tclass._module.Node()), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Test(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    n#0: ref
       where $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap), 
    nodes#0: Set Box
       where $Is(nodes#0, TSet(Tclass._module.Node()))
         && $IsAlloc(nodes#0, TSet(Tclass._module.Node()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Test(this: ref, n#0: ref, nodes#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##r#0: Set Box;
  var ##r#1: Set Box;

    // AddMethodImpl: Test, Impl$$_module.Node.Test
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(16,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(17,5)
    assume true;
    assume Set#Equal(nodes#0, Set#Difference(nodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(20,5)
    ##r#0 := nodes#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#0, TSet(Tclass._module.Node()), $Heap);
    assume _module.Node.IsList#canCall($Heap, this, nodes#0);
    ##r#1 := Set#Difference(nodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#1, TSet(Tclass._module.Node()), $Heap);
    assume _module.Node.IsList#canCall($Heap, 
      this, 
      Set#Difference(nodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))));
    assume _module.Node.IsList#canCall($Heap, this, nodes#0)
       && _module.Node.IsList#canCall($Heap, 
        this, 
        Set#Difference(nodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))));
    assert {:subsumption 0} _module.Node.IsList($LS($LS($LZ)), $Heap, this, nodes#0)
       == _module.Node.IsList($LS($LS($LZ)), 
        $Heap, 
        this, 
        Set#Difference(nodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))));
    assume _module.Node.IsList($LS($LZ), $Heap, this, nodes#0)
       == _module.Node.IsList($LS($LZ), 
        $Heap, 
        this, 
        Set#Difference(nodes#0, Set#UnionOne(Set#Empty(): Set Box, $Box(n#0))));
}



procedure CheckWellformed$$_module.Node.Create(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.Create(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Create(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Create(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.Node?());
  var defass#tmp#0: bool;
  var tmp#0: ref
     where defass#tmp#0
       ==> $Is(tmp#0, Tclass._module.Node())
         && $IsAlloc(tmp#0, Tclass._module.Node(), $Heap);
  var $nw: ref;

    // AddMethodImpl: Create, Impl$$_module.Node.Create
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(25,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(26,10)
    assume true;
    assert $_Frame[this, _module.Node.next];
    assume true;
    $rhs#0 := null;
    $Heap := update($Heap, this, _module.Node.next, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(26,16)"} true;
    havoc tmp#0 /* where defass#tmp#0
       ==> $Is(tmp#0, Tclass._module.Node())
         && $IsAlloc(tmp#0, Tclass._module.Node(), $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(28,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    tmp#0 := $nw;
    defass#tmp#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(28,19)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(29,5)
    assert defass#tmp#0;
    assume true;
    assert tmp#0 != this;
}



procedure CheckWellformed$$_module.Node.SequenceUpdateOutOfBounds(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    s#0: Seq Box
       where $Is(s#0, TSeq(TSet(TInt))) && $IsAlloc(s#0, TSeq(TSet(TInt)), $Heap), 
    j#0: int)
   returns (t#0: Seq Box
       where $Is(t#0, TSeq(TSet(TInt))) && $IsAlloc(t#0, TSeq(TSet(TInt)), $Heap));
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.SequenceUpdateOutOfBounds(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    s#0: Seq Box
       where $Is(s#0, TSeq(TSet(TInt))) && $IsAlloc(s#0, TSeq(TSet(TInt)), $Heap), 
    j#0: int)
   returns (t#0: Seq Box
       where $Is(t#0, TSeq(TSet(TInt))) && $IsAlloc(t#0, TSeq(TSet(TInt)), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.SequenceUpdateOutOfBounds(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    s#0: Seq Box
       where $Is(s#0, TSeq(TSet(TInt))) && $IsAlloc(s#0, TSeq(TSet(TInt)), $Heap), 
    j#0: int)
   returns (t#0: Seq Box
       where $Is(t#0, TSeq(TSet(TInt))) && $IsAlloc(t#0, TSeq(TSet(TInt)), $Heap), 
    $_reverifyPost: bool);
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.SequenceUpdateOutOfBounds(this: ref, s#0: Seq Box, j#0: int) returns (t#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: SequenceUpdateOutOfBounds, Impl$$_module.Node.SequenceUpdateOutOfBounds
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(33,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(34,7)
    assume true;
    assert 0 <= j#0 && j#0 < Seq#Length(s#0);
    assume true;
    t#0 := Seq#Update(s#0, j#0, $Box(Lit(Set#Empty(): Set Box)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(34,19)"} true;
}



procedure CheckWellformed$$_module.Node.Sequence(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    s#0: Seq Box where $Is(s#0, TSeq(TBool)) && $IsAlloc(s#0, TSeq(TBool), $Heap), 
    j#0: int, 
    b#0: bool, 
    c#0: bool)
   returns (t#0: Seq Box where $Is(t#0, TSeq(TBool)) && $IsAlloc(t#0, TSeq(TBool), $Heap));
  free requires 55 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.Sequence(this: ref, s#0: Seq Box, j#0: int, b#0: bool, c#0: bool) returns (t#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Sequence, CheckWellformed$$_module.Node.Sequence
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(37,9): initial state"} true;
    assume LitInt(10) <= Seq#Length(s#0);
    if (LitInt(8) <= j#0)
    {
    }

    assume LitInt(8) <= j#0 && j#0 < Seq#Length(s#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc t#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(40,16): post-state"} true;
    assume Seq#Length(t#0) == Seq#Length(s#0);
    if (*)
    {
        assert 0 <= LitInt(8) && LitInt(8) < Seq#Length(t#0);
        assert 0 <= LitInt(8) && LitInt(8) < Seq#Length(s#0);
        assume $Unbox(Seq#Index(t#0, LitInt(8))): bool
           == $Unbox(Seq#Index(s#0, LitInt(8))): bool;
    }
    else
    {
        assume $Unbox(Seq#Index(t#0, LitInt(8))): bool
           != $Unbox(Seq#Index(s#0, LitInt(8))): bool;
        assert 0 <= LitInt(9) && LitInt(9) < Seq#Length(t#0);
        assert 0 <= LitInt(9) && LitInt(9) < Seq#Length(s#0);
        assume $Unbox(Seq#Index(t#0, LitInt(9))): bool
           == $Unbox(Seq#Index(s#0, LitInt(9))): bool;
    }

    assert 0 <= j#0 && j#0 < Seq#Length(t#0);
    assume $Unbox(Seq#Index(t#0, j#0)): bool == b#0;
}



procedure Call$$_module.Node.Sequence(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    s#0: Seq Box where $Is(s#0, TSeq(TBool)) && $IsAlloc(s#0, TSeq(TBool), $Heap), 
    j#0: int, 
    b#0: bool, 
    c#0: bool)
   returns (t#0: Seq Box where $Is(t#0, TSeq(TBool)) && $IsAlloc(t#0, TSeq(TBool), $Heap));
  // user-defined preconditions
  requires LitInt(10) <= Seq#Length(s#0);
  requires LitInt(8) <= j#0;
  requires j#0 < Seq#Length(s#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(t#0) == Seq#Length(s#0);
  free ensures true;
  ensures $Unbox(Seq#Index(t#0, LitInt(8))): bool
       == $Unbox(Seq#Index(s#0, LitInt(8))): bool
     || $Unbox(Seq#Index(t#0, LitInt(9))): bool
       == $Unbox(Seq#Index(s#0, LitInt(9))): bool;
  free ensures true;
  ensures $Unbox(Seq#Index(t#0, j#0)): bool == b#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Sequence(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    s#0: Seq Box where $Is(s#0, TSeq(TBool)) && $IsAlloc(s#0, TSeq(TBool), $Heap), 
    j#0: int, 
    b#0: bool, 
    c#0: bool)
   returns (t#0: Seq Box where $Is(t#0, TSeq(TBool)) && $IsAlloc(t#0, TSeq(TBool), $Heap), 
    $_reverifyPost: bool);
  free requires 55 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(10) <= Seq#Length(s#0);
  requires LitInt(8) <= j#0;
  requires j#0 < Seq#Length(s#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Length(t#0) == Seq#Length(s#0);
  free ensures true;
  ensures $Unbox(Seq#Index(t#0, LitInt(8))): bool
       == $Unbox(Seq#Index(s#0, LitInt(8))): bool
     || $Unbox(Seq#Index(t#0, LitInt(9))): bool
       == $Unbox(Seq#Index(s#0, LitInt(9))): bool;
  free ensures true;
  ensures $Unbox(Seq#Index(t#0, j#0)): bool == b#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Sequence(this: ref, s#0: Seq Box, j#0: int, b#0: bool, c#0: bool)
   returns (t#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Sequence, Impl$$_module.Node.Sequence
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(43,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(44,5)
    assume true;
    if (c#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(45,9)
        assume true;
        assert 0 <= j#0 && j#0 < Seq#Length(s#0);
        assume true;
        t#0 := Seq#Update(s#0, j#0, $Box(b#0));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(45,20)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(47,9)
        assume true;
        assert 0 <= j#0 && j#0 <= Seq#Length(s#0);
        assert 0 <= j#0 + 1 && j#0 + 1 <= Seq#Length(s#0);
        assume true;
        t#0 := Seq#Append(Seq#Append(Seq#Take(s#0, j#0), Seq#Build(Seq#Empty(): Seq Box, $Box(b#0))), 
          Seq#Drop(s#0, j#0 + 1));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(47,34)"} true;
    }
}



procedure CheckWellformed$$_module.Node.Max0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int, 
    y#0: int)
   returns (r#0: int);
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.Max0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int, 
    y#0: int)
   returns (r#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == (if x#0 < y#0 then y#0 else x#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Max0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int, 
    y#0: int)
   returns (r#0: int, $_reverifyPost: bool);
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == (if x#0 < y#0 then y#0 else x#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Max0(this: ref, x#0: int, y#0: int) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Max0, Impl$$_module.Node.Max0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(53,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(54,5)
    assume true;
    if (x#0 < y#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(54,20)
        assume true;
        assume true;
        r#0 := y#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(54,23)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(54,37)
        assume true;
        assume true;
        r#0 := x#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(54,40)"} true;
    }
}



procedure CheckWellformed$$_module.Node.Max1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int, 
    y#0: int)
   returns (r#0: int);
  free requires 57 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Node.Max1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int, 
    y#0: int)
   returns (r#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == x#0 || r#0 == y#0;
  free ensures true;
  ensures x#0 <= r#0;
  ensures y#0 <= r#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Node.Max1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int, 
    y#0: int)
   returns (r#0: int, $_reverifyPost: bool);
  free requires 57 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r#0 == x#0 || r#0 == y#0;
  free ensures true;
  ensures x#0 <= r#0;
  ensures y#0 <= r#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Node.Max1(this: ref, x#0: int, y#0: int) returns (r#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Max1, Impl$$_module.Node.Max1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(60,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(61,7)
    assume true;
    if (x#0 < y#0)
    {
    }
    else
    {
    }

    assume true;
    r#0 := (if x#0 < y#0 then y#0 else x#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(61,31)"} true;
}



// function declaration for _module.Node.PoorlyDefined
function _module.Node.PoorlyDefined($heap: Heap, this: ref, x#0: int) : int;

function _module.Node.PoorlyDefined#canCall($heap: Heap, this: ref, x#0: int) : bool;

// frame axiom for _module.Node.PoorlyDefined
axiom (forall $h0: Heap, $h1: Heap, this: ref, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Node.PoorlyDefined($h1, this, x#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Node())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || $o == read($h0, this, _module.Node.next))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Node.PoorlyDefined($h0, this, x#0)
       == _module.Node.PoorlyDefined($h1, this, x#0));

// consequence axiom for _module.Node.PoorlyDefined
axiom 58 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.Node.PoorlyDefined($Heap, this, x#0) } 
    _module.Node.PoorlyDefined#canCall($Heap, this, x#0)
         || (58 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap)
           && 
          (if read($Heap, this, _module.Node.next) == null
             then Div(5, x#0) < 20
             else true)
           && (if read($Heap, this, _module.Node.next) == null
             then true
             else LitInt(0) <= Div(5, x#0))
           && (if read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) == null
             then true
             else true)
           && Div(10, x#0) != 8)
       ==> true);

function _module.Node.PoorlyDefined#requires(Heap, ref, int) : bool;

// #requires axiom for _module.Node.PoorlyDefined
axiom (forall $Heap: Heap, this: ref, x#0: int :: 
  { _module.Node.PoorlyDefined#requires($Heap, this, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Node())
       && $IsAlloc(this, Tclass._module.Node(), $Heap)
     ==> _module.Node.PoorlyDefined#requires($Heap, this, x#0)
       == (
        (if read($Heap, this, _module.Node.next) == null
           then Div(5, x#0) < 20
           else true)
         && (if read($Heap, this, _module.Node.next) == null
           then true
           else LitInt(0) <= Div(5, x#0))
         && (if read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) == null
           then true
           else true)
         && Div(10, x#0) != 8));

// definition axiom for _module.Node.PoorlyDefined (revealed)
axiom 58 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref, x#0: int :: 
    { _module.Node.PoorlyDefined($Heap, this, x#0), $IsGoodHeap($Heap) } 
    _module.Node.PoorlyDefined#canCall($Heap, this, x#0)
         || (58 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Node())
           && $IsAlloc(this, Tclass._module.Node(), $Heap)
           && 
          (if read($Heap, this, _module.Node.next) == null
             then Div(5, x#0) < 20
             else true)
           && (if read($Heap, this, _module.Node.next) == null
             then true
             else LitInt(0) <= Div(5, x#0))
           && (if read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) == null
             then true
             else true)
           && Div(10, x#0) != 8)
       ==> _module.Node.PoorlyDefined($Heap, this, x#0) == LitInt(12));

procedure CheckWellformed$$_module.Node.PoorlyDefined(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Node())
         && $IsAlloc(this, Tclass._module.Node(), $Heap), 
    x#0: int);
  free requires 58 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Node.PoorlyDefined(this: ref, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;
  var b$reqreads#4: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;
    b$reqreads#4 := true;

    // AddWellformednessCheck for function PoorlyDefined
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(64,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this || $o == read($Heap, this, _module.Node.next));
    if (*)
    {
        b$reqreads#0 := $_Frame[this, _module.Node.next];
        assume read($Heap, this, _module.Node.next) == null;
        assert x#0 != 0;
        assume Div(5, x#0) < 20;
    }
    else
    {
        assume read($Heap, this, _module.Node.next) != null;
        assume true;
    }

    if (*)
    {
        b$reqreads#1 := $_Frame[this, _module.Node.next];
        assume read($Heap, this, _module.Node.next) == null;
        assume true;
    }
    else
    {
        assume read($Heap, this, _module.Node.next) != null;
        assert x#0 != 0;
        assume LitInt(0) <= Div(5, x#0);
    }

    if (*)
    {
        b$reqreads#2 := $_Frame[this, _module.Node.next];
        assert read($Heap, this, _module.Node.next) != null;
        b$reqreads#3 := $_Frame[read($Heap, this, _module.Node.next), _module.Node.next];
        assume read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) == null;
        assume true;
    }
    else
    {
        assume read($Heap, read($Heap, this, _module.Node.next), _module.Node.next) != null;
        assume true;
    }

    assert x#0 != 0;
    assume Div(10, x#0) != 8;
    assert b$reqreads#0;
    assert b$reqreads#1;
    assert b$reqreads#2;
    assert b$reqreads#3;
    b$reqreads#4 := $_Frame[this, _module.Node.next];
    assert b$reqreads#4;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> $o == this || $o == read($Heap, this, _module.Node.next));
        assume _module.Node.PoorlyDefined($Heap, this, x#0) == LitInt(12);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Node.PoorlyDefined($Heap, this, x#0), TInt);
    }
}



// _module.Node: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Node()) } 
  $Is(c#0, Tclass._module.Node())
     <==> $Is(c#0, Tclass._module.Node?()) && c#0 != null);

// _module.Node: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Node(), $h) } 
  $IsAlloc(c#0, Tclass._module.Node(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Node?(), $h));

const unique class._module.Modifies?: ClassName;

function Tclass._module.Modifies?() : Ty;

const unique Tagclass._module.Modifies?: TyTag;

// Tclass._module.Modifies? Tag
axiom Tag(Tclass._module.Modifies?()) == Tagclass._module.Modifies?
   && TagFamily(Tclass._module.Modifies?()) == tytagFamily$Modifies;

// Box/unbox axiom for Tclass._module.Modifies?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Modifies?()) } 
  $IsBox(bx, Tclass._module.Modifies?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Modifies?()));

// Modifies: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Modifies?()) } 
  $Is($o, Tclass._module.Modifies?())
     <==> $o == null || dtype($o) == Tclass._module.Modifies?());

// Modifies: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Modifies?(), $h) } 
  $IsAlloc($o, Tclass._module.Modifies?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Modifies.x) == 0
   && FieldOfDecl(class._module.Modifies?, field$x) == _module.Modifies.x
   && !$IsGhostField(_module.Modifies.x);

const _module.Modifies.x: Field int;

// Modifies.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Modifies.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Modifies?()
     ==> $Is(read($h, $o, _module.Modifies.x), TInt));

// Modifies.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Modifies.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Modifies?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Modifies.x), TInt, $h));

axiom FDim(_module.Modifies.next) == 0
   && FieldOfDecl(class._module.Modifies?, field$next) == _module.Modifies.next
   && !$IsGhostField(_module.Modifies.next);

const _module.Modifies.next: Field ref;

// Modifies.next: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Modifies.next) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Modifies?()
     ==> $Is(read($h, $o, _module.Modifies.next), Tclass._module.Modifies?()));

// Modifies.next: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Modifies.next) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Modifies?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Modifies.next), Tclass._module.Modifies?(), $h));

function Tclass._module.Modifies() : Ty;

const unique Tagclass._module.Modifies: TyTag;

// Tclass._module.Modifies Tag
axiom Tag(Tclass._module.Modifies()) == Tagclass._module.Modifies
   && TagFamily(Tclass._module.Modifies()) == tytagFamily$Modifies;

// Box/unbox axiom for Tclass._module.Modifies
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Modifies()) } 
  $IsBox(bx, Tclass._module.Modifies())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Modifies()));

procedure CheckWellformed$$_module.Modifies.A(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.A(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.A(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.A(this: ref, p#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $rhs#0_0: int;

    // AddMethodImpl: A, Impl$$_module.Modifies.A
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == p#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(83,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(84,7)
    assume true;
    assert $_Frame[this, _module.Modifies.x];
    assume true;
    $rhs#0 := read($Heap, this, _module.Modifies.x) + 1;
    $Heap := update($Heap, this, _module.Modifies.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(84,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(85,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 75 - read($Heap, p#0, _module.Modifies.x);
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this || $o == p#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant 75 - read($Heap, p#0, _module.Modifies.x) <= $decr_init$loop#00
         && (75 - read($Heap, p#0, _module.Modifies.x) == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(85,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assert p#0 != null;
            assume true;
            assume false;
        }

        if (p#0 != null)
        {
            assert p#0 != null;
        }

        assume true;
        if (!(p#0 != null && read($Heap, p#0, _module.Modifies.x) < 75))
        {
            break;
        }

        $decr$loop#00 := 75 - read($Heap, p#0, _module.Modifies.x);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(88,11)
        assert p#0 != null;
        assume true;
        assert $_Frame[p#0, _module.Modifies.x];
        assert p#0 != null;
        assume true;
        $rhs#0_0 := read($Heap, p#0, _module.Modifies.x) + 1;
        $Heap := update($Heap, p#0, _module.Modifies.x, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(88,20)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(85,5)
        assert 0 <= $decr$loop#00 || 75 - read($Heap, p#0, _module.Modifies.x) == $decr$loop#00;
        assert 75 - read($Heap, p#0, _module.Modifies.x) < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.Modifies.Aprime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap));
  free requires 59 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.Aprime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.Aprime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 59 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.Aprime(this: ref, p#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $rhs#0_0: int;

    // AddMethodImpl: Aprime, Impl$$_module.Modifies.Aprime
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == p#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(94,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(95,7)
    assume true;
    assert $_Frame[this, _module.Modifies.x];
    assume true;
    $rhs#0 := read($Heap, this, _module.Modifies.x) + 1;
    $Heap := update($Heap, this, _module.Modifies.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(95,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(96,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0);
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this || $o == p#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0)
           <= $decr_init$loop#00
         && ((if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0)
             == $decr_init$loop#00
           ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(96,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (p#0 != null)
            {
                assert p#0 != null;
            }
            else
            {
            }

            assume true;
            assume false;
        }

        if (p#0 != null)
        {
            assert p#0 != null;
        }

        assume true;
        if (!(p#0 != null && read($Heap, p#0, _module.Modifies.x) < 75))
        {
            break;
        }

        $decr$loop#00 := (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(99,11)
        assert p#0 != null;
        assume true;
        assert $_Frame[p#0, _module.Modifies.x];
        assert p#0 != null;
        assume true;
        $rhs#0_0 := read($Heap, p#0, _module.Modifies.x) + 1;
        $Heap := update($Heap, p#0, _module.Modifies.x, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(99,20)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(96,5)
        assert 0 <= $decr$loop#00
           || (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0)
             == $decr$loop#00;
        assert (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0)
           < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.Modifies.Adoubleprime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap));
  free requires 60 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.Adoubleprime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.Adoubleprime(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies?())
         && $IsAlloc(p#0, Tclass._module.Modifies?(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 60 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this || $o == p#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.Adoubleprime(this: ref, p#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $rhs#0_0: int;

    // AddMethodImpl: Adoubleprime, Impl$$_module.Modifies.Adoubleprime
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == p#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(105,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(106,7)
    assume true;
    assert $_Frame[this, _module.Modifies.x];
    assume true;
    $rhs#0 := read($Heap, this, _module.Modifies.x) + 1;
    $Heap := update($Heap, this, _module.Modifies.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(106,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(107,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0 - 1);
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this || $o == p#0);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0 - 1)
           <= $decr_init$loop#00
         && ((if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0 - 1)
             == $decr_init$loop#00
           ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(107,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (p#0 != null)
            {
                assert p#0 != null;
            }
            else
            {
            }

            assume true;
            assume false;
        }

        if (p#0 != null)
        {
            assert p#0 != null;
        }

        assume true;
        if (!(p#0 != null && read($Heap, p#0, _module.Modifies.x) < 75))
        {
            break;
        }

        $decr$loop#00 := (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0 - 1);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(109,11)
        assert p#0 != null;
        assume true;
        assert $_Frame[p#0, _module.Modifies.x];
        assert p#0 != null;
        assume true;
        $rhs#0_0 := read($Heap, p#0, _module.Modifies.x) + 1;
        $Heap := update($Heap, p#0, _module.Modifies.x, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(109,20)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(107,5)
        assert 0 <= $decr$loop#00
           || (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0 - 1)
             == $decr$loop#00;
        assert (if p#0 != null then 75 - read($Heap, p#0, _module.Modifies.x) else 0 - 1)
           < $decr$loop#00;
    }
}



procedure CheckWellformed$$_module.Modifies.B(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies())
         && $IsAlloc(p#0, Tclass._module.Modifies(), $Heap));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.B(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies())
         && $IsAlloc(p#0, Tclass._module.Modifies(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.B(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies())
         && $IsAlloc(p#0, Tclass._module.Modifies(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.B(this: ref, p#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p##0: ref;
  var p##0_0: ref;
  var p##1: ref;

    // AddMethodImpl: B, Impl$$_module.Modifies.B
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(115,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(116,6)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##0 := this;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && ($o == this || $o == p##0)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Modifies.A(this, p##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(116,11)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(117,5)
    assume true;
    if (p#0 == this)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(118,10)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert p#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0_0 := p#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && ($o == p#0 || $o == p##0_0)
             ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.Modifies.A(p#0, p##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(118,12)"} true;
    }
    else
    {
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(120,6)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##1 := p#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && ($o == this || $o == p##1)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Modifies.A(this, p##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(120,8)"} true;
}



procedure CheckWellformed$$_module.Modifies.C(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    b#0: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Modifies.C(this: ref, b#0: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: C, CheckWellformed$$_module.Modifies.C
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(123,9): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(125,15): post-state"} true;
    if (*)
    {
        assume !b#0;
        assert $IsAlloc(this, Tclass._module.Modifies(), old($Heap));
        assume read($Heap, this, _module.Modifies.x)
           == read(old($Heap), this, _module.Modifies.x);
        assert $IsAlloc(this, Tclass._module.Modifies(), old($Heap));
        assume read($Heap, this, _module.Modifies.next)
           == read(old($Heap), this, _module.Modifies.next);
    }
    else
    {
        assume !b#0
           ==> read($Heap, this, _module.Modifies.x)
               == read(old($Heap), this, _module.Modifies.x)
             && read($Heap, this, _module.Modifies.next)
               == read(old($Heap), this, _module.Modifies.next);
    }
}



procedure Call$$_module.Modifies.C(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    b#0: bool);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures !b#0
     ==> read($Heap, this, _module.Modifies.x)
       == read(old($Heap), this, _module.Modifies.x);
  ensures !b#0
     ==> read($Heap, this, _module.Modifies.next)
       == read(old($Heap), this, _module.Modifies.next);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.C(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    b#0: bool)
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures !b#0
     ==> read($Heap, this, _module.Modifies.x)
       == read(old($Heap), this, _module.Modifies.x);
  ensures !b#0
     ==> read($Heap, this, _module.Modifies.next)
       == read(old($Heap), this, _module.Modifies.next);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.C(this: ref, b#0: bool) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: C, Impl$$_module.Modifies.C
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(126,2): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.Modifies.D(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies())
         && $IsAlloc(p#0, Tclass._module.Modifies(), $Heap), 
    y#0: int);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.D(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies())
         && $IsAlloc(p#0, Tclass._module.Modifies(), $Heap), 
    y#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.D(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    p#0: ref
       where $Is(p#0, Tclass._module.Modifies())
         && $IsAlloc(p#0, Tclass._module.Modifies(), $Heap), 
    y#0: int)
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.D(this: ref, p#0: ref, y#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b##0_0: bool;
  var b##0: bool;

    // AddMethodImpl: D, Impl$$_module.Modifies.D
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(130,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(131,5)
    assume true;
    if (y#0 == LitInt(3))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(132,10)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert p#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##0_0 := Lit(true);
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == p#0 ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.Modifies.C(p#0, b##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(132,15)"} true;
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(134,10)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert p#0 != null;
        assume true;
        // ProcessCallStmt: CheckSubrange
        b##0 := Lit(false);
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == p#0 ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.Modifies.C(p#0, b##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(134,16)"} true;
    }
}



procedure CheckWellformed$$_module.Modifies.E(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.E(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.E(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.E(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p##0: ref;

    // AddMethodImpl: E, Impl$$_module.Modifies.E
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(143,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(144,6)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    p##0 := null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && ($o == this || $o == p##0)
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.Modifies.A(this, p##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(144,11)"} true;
}



procedure CheckWellformed$$_module.Modifies.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.Modifies()))
         && $IsAlloc(s#0, TSet(Tclass._module.Modifies()), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.Modifies()))
         && $IsAlloc(s#0, TSet(Tclass._module.Modifies()), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || s#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.Modifies()))
         && $IsAlloc(s#0, TSet(Tclass._module.Modifies()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || s#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.F(this: ref, s#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: ref;
  var m#1: ref;
  var $prevHeap: Heap;
  var $rhs#0_0: int;

    // AddMethodImpl: F, Impl$$_module.Modifies.F
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> s#0[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(149,2): initial state"} true;
    $_reverifyPost := false;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(150,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc m#0;
        assume $Is(m#0, Tclass._module.Modifies());
        if (s#0[$Box(m#0)])
        {
            assert {:subsumption 0} m#0 != null;
        }

        assume true;
        assume s#0[$Box(m#0)] && LitInt(2) <= read($Heap, m#0, _module.Modifies.x);
        assert {:subsumption 0} m#0 != null;
        assume true;
        assert $_Frame[m#0, _module.Modifies.x];
        assert {:subsumption 0} m#0 != null;
        assume true;
        havoc m#1;
        assume $Is(m#1, Tclass._module.Modifies());
        assume s#0[$Box(m#1)] && LitInt(2) <= read($Heap, m#1, _module.Modifies.x);
        assume m#0 != m#1;
        assert m#0 != m#1
           || _module.Modifies.x != _module.Modifies.x
           || read($Heap, m#0, _module.Modifies.x) + 1
             == read($Heap, m#1, _module.Modifies.x) + 1;
        assume false;
    }
    else
    {
        $prevHeap := $Heap;
        havoc $Heap;
        assume $HeapSucc($prevHeap, $Heap);
        assume (forall<alpha> $o: ref, $f: Field alpha :: 
          { read($Heap, $o, $f) } 
          read($Heap, $o, $f) == read($prevHeap, $o, $f)
             || (exists m#2: ref :: 
              $Is(m#2, Tclass._module.Modifies())
                 && 
                s#0[$Box(m#2)]
                 && LitInt(2) <= read($prevHeap, m#2, _module.Modifies.x)
                 && $o == m#2
                 && $f == _module.Modifies.x));
        assume (forall m#inv#0: ref :: 
          { read($Heap, m#inv#0, _module.Modifies.x) } 
          $Is(m#inv#0, Tclass._module.Modifies())
               && 
              m#inv#0 != null
               && 
              s#0[$Box(m#inv#0)]
               && LitInt(2) <= read($prevHeap, m#inv#0, _module.Modifies.x)
             ==> read($Heap, m#inv#0, _module.Modifies.x)
               == read($prevHeap, m#inv#0, _module.Modifies.x) + 1);
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(152,4)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(153,5)
    assume true;
    if (s#0[$Box(this)])
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(154,9)
        assume true;
        assert $_Frame[this, _module.Modifies.x];
        assume true;
        $rhs#0_0 := Mul(LitInt(2), read($Heap, this, _module.Modifies.x));
        $Heap := update($Heap, this, _module.Modifies.x, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(154,16)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.Modifies.G(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.Modifies()))
         && $IsAlloc(s#0, TSet(Tclass._module.Modifies()), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.G(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.Modifies()))
         && $IsAlloc(s#0, TSet(Tclass._module.Modifies()), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.G(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(Tclass._module.Modifies()))
         && $IsAlloc(s#0, TSet(Tclass._module.Modifies()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.G(this: ref, s#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#0: int;
  var m#1: ref;
  var m#2: ref;
  var $prevHeap: Heap;
  var m#0_0: ref;
  var m#0_1: ref;
  var s##0_0: Set Box;
  var m#4: ref;
  var m#6: ref;
  var m#7: ref;

    // AddMethodImpl: G, Impl$$_module.Modifies.G
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(160,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(161,11)
    assume true;
    assume true;
    m#0 := LitInt(3);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(161,14)"} true;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(163,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc m#1;
        assume $Is(m#1, Tclass._module.Modifies());
        if (s#0[$Box(m#1)])
        {
        }

        assume true;
        assume s#0[$Box(m#1)] && m#1 == this;
        assert {:subsumption 0} m#1 != null;
        assume true;
        assert $_Frame[m#1, _module.Modifies.x];
        assert {:subsumption 0} m#1 != null;
        assume true;
        havoc m#2;
        assume $Is(m#2, Tclass._module.Modifies());
        assume s#0[$Box(m#2)] && m#2 == this;
        assume m#1 != m#2;
        assert m#1 != m#2
           || _module.Modifies.x != _module.Modifies.x
           || read($Heap, m#1, _module.Modifies.x) + 1
             == read($Heap, m#2, _module.Modifies.x) + 1;
        assume false;
    }
    else
    {
        $prevHeap := $Heap;
        havoc $Heap;
        assume $HeapSucc($prevHeap, $Heap);
        assume (forall<alpha> $o: ref, $f: Field alpha :: 
          { read($Heap, $o, $f) } 
          read($Heap, $o, $f) == read($prevHeap, $o, $f)
             || (exists m#3: ref :: 
              $Is(m#3, Tclass._module.Modifies())
                 && 
                s#0[$Box(m#3)]
                 && m#3 == this
                 && $o == m#3
                 && $f == _module.Modifies.x));
        assume (forall m#inv#0: ref :: 
          { read($Heap, m#inv#0, _module.Modifies.x) } 
          $Is(m#inv#0, Tclass._module.Modifies())
               && 
              m#inv#0 != null
               && 
              s#0[$Box(m#inv#0)]
               && m#inv#0 == this
             ==> read($Heap, m#inv#0, _module.Modifies.x)
               == read($prevHeap, m#inv#0, _module.Modifies.x) + 1);
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(165,4)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(166,5)
    assume true;
    if (Set#Subset(s#0, Set#UnionOne(Set#Empty(): Set Box, $Box(this))))
    {
        // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(167,7)
        if (*)
        {
            // Assume Fuel Constant
            havoc m#0_0;
            assume $Is(m#0_0, Tclass._module.Modifies());
            assume true;
            assume s#0[$Box(m#0_0)];
            assert {:subsumption 0} m#0_0 != null;
            assume true;
            assert $_Frame[m#0_0, _module.Modifies.x];
            assert {:subsumption 0} m#0_0 != null;
            assume true;
            havoc m#0_1;
            assume $Is(m#0_1, Tclass._module.Modifies());
            assume s#0[$Box(m#0_1)];
            assume m#0_0 != m#0_1;
            assert m#0_0 != m#0_1
               || _module.Modifies.x != _module.Modifies.x
               || read($Heap, m#0_0, _module.Modifies.x) + 1
                 == read($Heap, m#0_1, _module.Modifies.x) + 1;
            assume false;
        }
        else
        {
            $prevHeap := $Heap;
            havoc $Heap;
            assume $HeapSucc($prevHeap, $Heap);
            assume (forall<alpha> $o: ref, $f: Field alpha :: 
              { read($Heap, $o, $f) } 
              read($Heap, $o, $f) == read($prevHeap, $o, $f)
                 || (exists m#0_2: ref :: 
                  $Is(m#0_2, Tclass._module.Modifies())
                     && s#0[$Box(m#0_2)]
                     && $o == m#0_2
                     && $f == _module.Modifies.x));
            assume (forall m#inv#0_0: ref :: 
              { read($Heap, m#inv#0_0, _module.Modifies.x) } 
              $Is(m#inv#0_0, Tclass._module.Modifies())
                   && 
                  m#inv#0_0 != null
                   && s#0[$Box(m#inv#0_0)]
                 ==> read($Heap, m#inv#0_0, _module.Modifies.x)
                   == read($prevHeap, m#inv#0_0, _module.Modifies.x) + 1);
        }

        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(169,6)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(170,8)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0_0 := s#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && s##0_0[$Box($o)] ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.Modifies.F(this, s##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(170,10)"} true;
    }
    else
    {
    }

    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(172,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc m#4;
        assume $Is(m#4, Tclass._module.Modifies());
        assume true;
        assume s#0[$Box(m#4)];
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(172,41)
        assert {:subsumption 0} m#4 != null;
        assert {:subsumption 0} m#4 != null;
        assume true;
        assert read($Heap, m#4, _module.Modifies.x) < read($Heap, m#4, _module.Modifies.x) + 10;
        assert true;
        assume false;
    }
    else
    {
        assume (forall m#5: ref :: 
          { s#0[$Box(m#5)] } 
          $Is(m#5, Tclass._module.Modifies()) && s#0[$Box(m#5)] ==> Lit(true));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(172,63)"} true;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(173,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc m#6;
        assume $Is(m#6, Tclass._module.Modifies());
        assume true;
        assume s#0[$Box(m#6)];
        assert {:subsumption 0} m#6 != null;
        assume true;
        assert $_Frame[m#6, _module.Modifies.x];
        assert {:subsumption 0} m#6 != null;
        assume true;
        havoc m#7;
        assume $Is(m#7, Tclass._module.Modifies());
        assume s#0[$Box(m#7)];
        assume m#6 != m#7;
        assert m#6 != m#7
           || _module.Modifies.x != _module.Modifies.x
           || read($Heap, m#6, _module.Modifies.x) + 1
             == read($Heap, m#7, _module.Modifies.x) + 1;
        assume false;
    }
    else
    {
        $prevHeap := $Heap;
        havoc $Heap;
        assume $HeapSucc($prevHeap, $Heap);
        assume (forall<alpha> $o: ref, $f: Field alpha :: 
          { read($Heap, $o, $f) } 
          read($Heap, $o, $f) == read($prevHeap, $o, $f)
             || (exists m#8: ref :: 
              $Is(m#8, Tclass._module.Modifies())
                 && s#0[$Box(m#8)]
                 && $o == m#8
                 && $f == _module.Modifies.x));
        assume (forall m#inv#1: ref :: 
          { read($Heap, m#inv#1, _module.Modifies.x) } 
          $Is(m#inv#1, Tclass._module.Modifies()) && m#inv#1 != null && s#0[$Box(m#inv#1)]
             ==> read($Heap, m#inv#1, _module.Modifies.x)
               == read($prevHeap, m#inv#1, _module.Modifies.x) + 1);
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(175,4)"} true;
}



procedure CheckWellformed$$_module.Modifies.SetConstruction(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap));
  free requires 61 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Modifies.SetConstruction(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Modifies.SetConstruction(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Modifies())
         && $IsAlloc(this, Tclass._module.Modifies(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 61 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Modifies.SetConstruction(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap);

    // AddMethodImpl: SetConstruction, Impl$$_module.Modifies.SetConstruction
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(178,27): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(179,11)
    assume true;
    assume true;
    s#0 := Lit(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(1))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(179,16)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(180,5)
    assume true;
    assert !Set#Equal(s#0, Set#Empty(): Set Box);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(181,5)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(182,7)
        assume true;
        assert !Set#Equal(s#0, 
          Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(0))), $Box(LitInt(1))));
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(184,7)
        assume true;
        assert !Set#Equal(s#0, 
          Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(1))), $Box(LitInt(0))));
    }
}



// _module.Modifies: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Modifies()) } 
  $Is(c#0, Tclass._module.Modifies())
     <==> $Is(c#0, Tclass._module.Modifies?()) && c#0 != null);

// _module.Modifies: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Modifies(), $h) } 
  $IsAlloc(c#0, Tclass._module.Modifies(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Modifies?(), $h));

const unique class._module.AllocatedTests?: ClassName;

function Tclass._module.AllocatedTests?() : Ty;

const unique Tagclass._module.AllocatedTests?: TyTag;

// Tclass._module.AllocatedTests? Tag
axiom Tag(Tclass._module.AllocatedTests?()) == Tagclass._module.AllocatedTests?
   && TagFamily(Tclass._module.AllocatedTests?()) == tytagFamily$AllocatedTests;

// Box/unbox axiom for Tclass._module.AllocatedTests?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AllocatedTests?()) } 
  $IsBox(bx, Tclass._module.AllocatedTests?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AllocatedTests?()));

// AllocatedTests: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.AllocatedTests?()) } 
  $Is($o, Tclass._module.AllocatedTests?())
     <==> $o == null || dtype($o) == Tclass._module.AllocatedTests?());

// AllocatedTests: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.AllocatedTests?(), $h) } 
  $IsAlloc($o, Tclass._module.AllocatedTests?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.AllocatedTests() : Ty;

const unique Tagclass._module.AllocatedTests: TyTag;

// Tclass._module.AllocatedTests Tag
axiom Tag(Tclass._module.AllocatedTests()) == Tagclass._module.AllocatedTests
   && TagFamily(Tclass._module.AllocatedTests()) == tytagFamily$AllocatedTests;

// Box/unbox axiom for Tclass._module.AllocatedTests
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AllocatedTests()) } 
  $IsBox(bx, Tclass._module.AllocatedTests())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AllocatedTests()));

procedure CheckWellformed$$_module.AllocatedTests.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AllocatedTests.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AllocatedTests.M(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AllocatedTests.M(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
  var $nw: ref;

    // AddMethodImpl: M, Impl$$_module.AllocatedTests.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(193,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(194,11)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    n#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(194,21)"} true;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(195,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(196,19)
        assume true;
        assert $IsAlloc(n#0, Tclass._module.Node?(), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(197,19)
        assume true;
        assert !(n#0 != null && !read(old($Heap), n#0, alloc));
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(198,19)
        if (n#0 != null && !read(old($Heap), n#0, alloc))
        {
        }

        if (n#0 != null
           && !read(old($Heap), n#0, alloc)
           && !$IsAlloc(n#0, Tclass._module.Node?(), old($Heap)))
        {
        }

        assume true;
        assert {:subsumption 0} n#0 != null && !read(old($Heap), n#0, alloc);
        assert {:subsumption 0} !$IsAlloc(n#0, Tclass._module.Node?(), old($Heap));
        assert {:subsumption 0} $IsAlloc(n#0, Tclass._module.Node?(), $Heap);
        assume n#0 != null
           && !read(old($Heap), n#0, alloc)
           && !$IsAlloc(n#0, Tclass._module.Node?(), old($Heap))
           && $IsAlloc(n#0, Tclass._module.Node?(), $Heap);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(199,19)
        assume true;
        assert null != null && !read(old($Heap), null, alloc);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(200,19)
        assume true;
        assert !(null != null && !read(old($Heap), null, alloc));
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(201,19)
        assume true;
        assert $IsAlloc(null, Tclass._System.object?(), $Heap);
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true) && !Lit(true);
        assert false;
    }
}



procedure CheckWellformed$$_module.AllocatedTests.Set0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AllocatedTests.Set0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AllocatedTests.Set0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AllocatedTests.Set0(this: ref, k#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
  var $nw: ref;
  var U#0: Set Box
     where $Is(U#0, TSet(Tclass._module.Node?()))
       && $IsAlloc(U#0, TSet(Tclass._module.Node?()), $Heap);

    // AddMethodImpl: Set0, Impl$$_module.AllocatedTests.Set0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(204,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(205,11)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    n#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(205,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(206,11)
    assume true;
    assume true;
    U#0 := Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(k#0)), $Box(n#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(206,18)"} true;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(207,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(208,19)
        assume true;
        assert $IsAlloc(U#0, TSet(Tclass._module.Node?()), $Heap);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(209,19)
        assume true;
        assert $IsAlloc(U#0, TSet(Tclass._module.Node?()), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(210,19)
        assume true;
        assert !$IsAlloc(U#0, TSet(Tclass._module.Node?()), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(211,19)
        assume true;
        assert (forall $o: ref :: 
          { U#0[$Box($o)] } 
          U#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else if (*)
    {
        assume true;
        assume k#0 == null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(212,24)
        assume true;
        assert (forall $o: ref :: 
          { U#0[$Box($o)] } 
          U#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else if (*)
    {
        assume true;
        assume k#0 == null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(213,24)
        assume true;
        assert !(forall $o: ref :: 
          { U#0[$Box($o)] } 
          U#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else if (*)
    {
        assume true;
        assume k#0 != null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(214,24)
        assume true;
        assert (forall $o: ref :: 
          { U#0[$Box($o)] } 
          U#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else if (*)
    {
        assume true;
        assume k#0 != null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(215,24)
        assume true;
        assert !(forall $o: ref :: 
          { U#0[$Box($o)] } 
          U#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && k#0 != null
           && k#0 != null
           && k#0 == null
           && k#0 == null;
        assert false;
    }
}



procedure CheckWellformed$$_module.AllocatedTests.Set1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node()) && $IsAlloc(k#0, Tclass._module.Node(), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AllocatedTests.Set1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node()) && $IsAlloc(k#0, Tclass._module.Node(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AllocatedTests.Set1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node()) && $IsAlloc(k#0, Tclass._module.Node(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AllocatedTests.Set1(this: ref, k#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap);
  var U#0: Set Box
     where $Is(U#0, TSet(Tclass._module.Node?()))
       && $IsAlloc(U#0, TSet(Tclass._module.Node?()), $Heap);

    // AddMethodImpl: Set1, Impl$$_module.AllocatedTests.Set1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(218,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(219,6)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AllocatedTests.M(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(219,7)"} true;
    havoc n#0 /* where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(221,11)
    assume true;
    assume true;
    U#0 := Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(k#0)), $Box(n#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(221,18)"} true;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(222,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(223,19)
        assume true;
        assert $IsAlloc(U#0, TSet(Tclass._module.Node?()), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume n#0 == null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(224,24)
        assume true;
        assert $IsAlloc(U#0, TSet(Tclass._module.Node?()), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume n#0 == null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(225,24)
        assume true;
        assert (forall $o: ref :: 
          { U#0[$Box($o)] } 
          U#0[$Box($o)] ==> $o != null && !read(old($Heap), $o, alloc));
    }
    else if (*)
    {
        assume true;
        assume !$IsAlloc(n#0, Tclass._module.Node?(), old($Heap));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(226,33)
        assume true;
        assert n#0 != null;
    }
    else if (*)
    {
        assume true;
        assume !$IsAlloc(n#0, Tclass._module.Node?(), old($Heap));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(227,33)
        assume true;
        assert n#0 != null && !read(old($Heap), n#0, alloc);
    }
    else if (*)
    {
        assume true;
        assume n#0 != null && !read(old($Heap), n#0, alloc);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(228,23)
        assume true;
        assert n#0 != null;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true)
           && n#0 != null
           && n#0 != null
           && $IsAlloc(n#0, Tclass._module.Node?(), old($Heap))
           && $IsAlloc(n#0, Tclass._module.Node?(), old($Heap))
           && !
          (n#0 != null
           && !read(old($Heap), n#0, alloc));
        assert false;
    }
}



procedure CheckWellformed$$_module.AllocatedTests.Seq0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AllocatedTests.Seq0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AllocatedTests.Seq0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AllocatedTests.Seq0(this: ref, k#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
  var $nw: ref;
  var U#0: Seq Box
     where $Is(U#0, TSeq(Tclass._module.Node?()))
       && $IsAlloc(U#0, TSeq(Tclass._module.Node?()), $Heap);

    // AddMethodImpl: Seq0, Impl$$_module.AllocatedTests.Seq0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(231,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(232,11)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    n#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(232,21)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(233,11)
    assume true;
    assume true;
    U#0 := Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(k#0)), $Box(n#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(233,18)"} true;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(234,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(235,19)
        assume true;
        assert $IsAlloc(U#0, TSeq(Tclass._module.Node?()), $Heap);
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(236,19)
        assume true;
        assert $IsAlloc(U#0, TSeq(Tclass._module.Node?()), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(237,19)
        assert {:subsumption 0} 0 <= LitInt(1) && LitInt(1) < Seq#Length(U#0);
        assume true;
        assert !$IsAlloc($Unbox(Seq#Index(U#0, LitInt(1))): ref, Tclass._module.Node?(), old($Heap));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(238,19)
        assume true;
        assert !$IsAlloc(U#0, TSeq(Tclass._module.Node?()), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(239,19)
        assume true;
        assert (forall $i: int :: 
          0 <= $i && $i < Seq#Length(U#0)
             ==> $Unbox(Seq#Index(U#0, $i)): ref != null
               && !read(old($Heap), $Unbox(Seq#Index(U#0, $i)): ref, alloc));
    }
    else if (*)
    {
        assume true;
        assume k#0 == null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(240,24)
        assume true;
        assert (forall $i: int :: 
          0 <= $i && $i < Seq#Length(U#0)
             ==> $Unbox(Seq#Index(U#0, $i)): ref != null
               && !read(old($Heap), $Unbox(Seq#Index(U#0, $i)): ref, alloc));
    }
    else if (*)
    {
        assume true;
        assume k#0 == null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(241,24)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(U#0);
        assume true;
        assert !($Unbox(Seq#Index(U#0, LitInt(0))): ref != null
           && !read(old($Heap), $Unbox(Seq#Index(U#0, LitInt(0))): ref, alloc));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(242,25)
        assume true;
        assert !(forall $i: int :: 
          0 <= $i && $i < Seq#Length(U#0)
             ==> $Unbox(Seq#Index(U#0, $i)): ref != null
               && !read(old($Heap), $Unbox(Seq#Index(U#0, $i)): ref, alloc));
    }
    else if (*)
    {
        assume true;
        assume k#0 != null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(243,24)
        assume true;
        assert (forall $i: int :: 
          0 <= $i && $i < Seq#Length(U#0)
             ==> $Unbox(Seq#Index(U#0, $i)): ref != null
               && !read(old($Heap), $Unbox(Seq#Index(U#0, $i)): ref, alloc));
    }
    else if (*)
    {
        assume true;
        assume k#0 != null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(244,24)
        assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(U#0);
        assume true;
        assert !($Unbox(Seq#Index(U#0, LitInt(0))): ref != null
           && !read(old($Heap), $Unbox(Seq#Index(U#0, LitInt(0))): ref, alloc));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(245,25)
        assume true;
        assert !(forall $i: int :: 
          0 <= $i && $i < Seq#Length(U#0)
             ==> $Unbox(Seq#Index(U#0, $i)): ref != null
               && !read(old($Heap), $Unbox(Seq#Index(U#0, $i)): ref, alloc));
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && !Lit(true)
           && k#0 != null
           && k#0 != null
           && k#0 == null
           && k#0 == null;
        assert false;
    }
}



procedure CheckWellformed$$_module.AllocatedTests.Seq1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AllocatedTests.Seq1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AllocatedTests.Seq1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AllocatedTests())
         && $IsAlloc(this, Tclass._module.AllocatedTests(), $Heap), 
    k#0: ref
       where $Is(k#0, Tclass._module.Node?()) && $IsAlloc(k#0, Tclass._module.Node?(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AllocatedTests.Seq1(this: ref, k#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap);
  var U#0: Seq Box
     where $Is(U#0, TSeq(Tclass._module.Node?()))
       && $IsAlloc(U#0, TSeq(Tclass._module.Node?()), $Heap);

    // AddMethodImpl: Seq1, Impl$$_module.AllocatedTests.Seq1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(248,2): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(249,6)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AllocatedTests.M(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(249,7)"} true;
    havoc n#0 /* where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(251,11)
    assume true;
    assume true;
    U#0 := Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(k#0)), $Box(n#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(251,18)"} true;
    // ----- alternative statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(252,5)
    if (*)
    {
        assume true;
        assume Lit(true);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(253,19)
        assume true;
        assert $IsAlloc(U#0, TSeq(Tclass._module.Node?()), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume n#0 == null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(254,24)
        assume true;
        assert $IsAlloc(U#0, TSeq(Tclass._module.Node?()), old($Heap));
    }
    else if (*)
    {
        assume true;
        assume n#0 == null;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(255,24)
        assume true;
        assert (forall $i: int :: 
          0 <= $i && $i < Seq#Length(U#0)
             ==> $Unbox(Seq#Index(U#0, $i)): ref != null
               && !read(old($Heap), $Unbox(Seq#Index(U#0, $i)): ref, alloc));
    }
    else if (*)
    {
        assume true;
        assume !$IsAlloc(n#0, Tclass._module.Node?(), old($Heap));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(256,33)
        assume true;
        assert n#0 != null;
    }
    else if (*)
    {
        assume true;
        assume !$IsAlloc(n#0, Tclass._module.Node?(), old($Heap));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(257,33)
        assume true;
        assert n#0 != null && !read(old($Heap), n#0, alloc);
    }
    else if (*)
    {
        assume true;
        assume n#0 != null && !read(old($Heap), n#0, alloc);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(258,23)
        assume true;
        assert n#0 != null;
    }
    else
    {
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume true;
        assume !Lit(true)
           && n#0 != null
           && n#0 != null
           && $IsAlloc(n#0, Tclass._module.Node?(), old($Heap))
           && $IsAlloc(n#0, Tclass._module.Node?(), old($Heap))
           && !
          (n#0 != null
           && !read(old($Heap), n#0, alloc));
        assert false;
    }
}



// _module.AllocatedTests: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.AllocatedTests()) } 
  $Is(c#0, Tclass._module.AllocatedTests())
     <==> $Is(c#0, Tclass._module.AllocatedTests?()) && c#0 != null);

// _module.AllocatedTests: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.AllocatedTests(), $h) } 
  $IsAlloc(c#0, Tclass._module.AllocatedTests(), $h)
     <==> $IsAlloc(c#0, Tclass._module.AllocatedTests?(), $h));

// Constructor function declaration
function #_module.Lindgren.Pippi(ref) : DatatypeType;

const unique ##_module.Lindgren.Pippi: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: ref :: 
  { #_module.Lindgren.Pippi(a#0#0#0) } 
  DatatypeCtorId(#_module.Lindgren.Pippi(a#0#0#0)) == ##_module.Lindgren.Pippi);

function _module.Lindgren.Pippi_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Lindgren.Pippi_q(d) } 
  _module.Lindgren.Pippi_q(d) <==> DatatypeCtorId(d) == ##_module.Lindgren.Pippi);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Lindgren.Pippi_q(d) } 
  _module.Lindgren.Pippi_q(d)
     ==> (exists a#1#0#0: ref :: d == #_module.Lindgren.Pippi(a#1#0#0)));

function Tclass._module.Lindgren() : Ty;

const unique Tagclass._module.Lindgren: TyTag;

// Tclass._module.Lindgren Tag
axiom Tag(Tclass._module.Lindgren()) == Tagclass._module.Lindgren
   && TagFamily(Tclass._module.Lindgren()) == tytagFamily$Lindgren;

// Box/unbox axiom for Tclass._module.Lindgren
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Lindgren()) } 
  $IsBox(bx, Tclass._module.Lindgren())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Lindgren()));

// Constructor $Is
axiom (forall a#2#0#0: ref :: 
  { $Is(#_module.Lindgren.Pippi(a#2#0#0), Tclass._module.Lindgren()) } 
  $Is(#_module.Lindgren.Pippi(a#2#0#0), Tclass._module.Lindgren())
     <==> $Is(a#2#0#0, Tclass._module.Node()));

// Constructor $IsAlloc
axiom (forall a#3#0#0: ref, $h: Heap :: 
  { $IsAlloc(#_module.Lindgren.Pippi(a#3#0#0), Tclass._module.Lindgren(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Lindgren.Pippi(a#3#0#0), Tclass._module.Lindgren(), $h)
       <==> $IsAlloc(a#3#0#0, Tclass._module.Node(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Lindgren._h0(d), Tclass._module.Node(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Lindgren.Pippi_q(d)
       && $IsAlloc(d, Tclass._module.Lindgren(), $h)
     ==> $IsAlloc(_module.Lindgren._h0(d), Tclass._module.Node(), $h));

// Constructor literal
axiom (forall a#4#0#0: ref :: 
  { #_module.Lindgren.Pippi(Lit(a#4#0#0)) } 
  #_module.Lindgren.Pippi(Lit(a#4#0#0)) == Lit(#_module.Lindgren.Pippi(a#4#0#0)));

function _module.Lindgren._h0(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#5#0#0: ref :: 
  { #_module.Lindgren.Pippi(a#5#0#0) } 
  _module.Lindgren._h0(#_module.Lindgren.Pippi(a#5#0#0)) == a#5#0#0);

// Constructor function declaration
function #_module.Lindgren.Longstocking(Seq Box, DatatypeType) : DatatypeType;

const unique ##_module.Lindgren.Longstocking: DtCtorId;

// Constructor identifier
axiom (forall a#6#0#0: Seq Box, a#6#1#0: DatatypeType :: 
  { #_module.Lindgren.Longstocking(a#6#0#0, a#6#1#0) } 
  DatatypeCtorId(#_module.Lindgren.Longstocking(a#6#0#0, a#6#1#0))
     == ##_module.Lindgren.Longstocking);

function _module.Lindgren.Longstocking_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Lindgren.Longstocking_q(d) } 
  _module.Lindgren.Longstocking_q(d)
     <==> DatatypeCtorId(d) == ##_module.Lindgren.Longstocking);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Lindgren.Longstocking_q(d) } 
  _module.Lindgren.Longstocking_q(d)
     ==> (exists a#7#0#0: Seq Box, a#7#1#0: DatatypeType :: 
      d == #_module.Lindgren.Longstocking(a#7#0#0, a#7#1#0)));

// Constructor $Is
axiom (forall a#8#0#0: Seq Box, a#8#1#0: DatatypeType :: 
  { $Is(#_module.Lindgren.Longstocking(a#8#0#0, a#8#1#0), Tclass._module.Lindgren()) } 
  $Is(#_module.Lindgren.Longstocking(a#8#0#0, a#8#1#0), Tclass._module.Lindgren())
     <==> $Is(a#8#0#0, TSeq(Tclass._System.object()))
       && $Is(a#8#1#0, Tclass._module.Lindgren()));

// Constructor $IsAlloc
axiom (forall a#9#0#0: Seq Box, a#9#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Lindgren.Longstocking(a#9#0#0, a#9#1#0), Tclass._module.Lindgren(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Lindgren.Longstocking(a#9#0#0, a#9#1#0), Tclass._module.Lindgren(), $h)
       <==> $IsAlloc(a#9#0#0, TSeq(Tclass._System.object()), $h)
         && $IsAlloc(a#9#1#0, Tclass._module.Lindgren(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Lindgren._h1(d), TSeq(Tclass._System.object()), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Lindgren.Longstocking_q(d)
       && $IsAlloc(d, Tclass._module.Lindgren(), $h)
     ==> $IsAlloc(_module.Lindgren._h1(d), TSeq(Tclass._System.object()), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Lindgren._h2(d), Tclass._module.Lindgren(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Lindgren.Longstocking_q(d)
       && $IsAlloc(d, Tclass._module.Lindgren(), $h)
     ==> $IsAlloc(_module.Lindgren._h2(d), Tclass._module.Lindgren(), $h));

// Constructor literal
axiom (forall a#10#0#0: Seq Box, a#10#1#0: DatatypeType :: 
  { #_module.Lindgren.Longstocking(Lit(a#10#0#0), Lit(a#10#1#0)) } 
  #_module.Lindgren.Longstocking(Lit(a#10#0#0), Lit(a#10#1#0))
     == Lit(#_module.Lindgren.Longstocking(a#10#0#0, a#10#1#0)));

function _module.Lindgren._h1(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#11#0#0: Seq Box, a#11#1#0: DatatypeType :: 
  { #_module.Lindgren.Longstocking(a#11#0#0, a#11#1#0) } 
  _module.Lindgren._h1(#_module.Lindgren.Longstocking(a#11#0#0, a#11#1#0))
     == a#11#0#0);

// Inductive seq element rank
axiom (forall a#12#0#0: Seq Box, a#12#1#0: DatatypeType, i: int :: 
  { Seq#Index(a#12#0#0, i), #_module.Lindgren.Longstocking(a#12#0#0, a#12#1#0) } 
  0 <= i && i < Seq#Length(a#12#0#0)
     ==> DtRank($Unbox(Seq#Index(a#12#0#0, i)): DatatypeType)
       < DtRank(#_module.Lindgren.Longstocking(a#12#0#0, a#12#1#0)));

// Inductive seq rank
axiom (forall a#13#0#0: Seq Box, a#13#1#0: DatatypeType :: 
  { #_module.Lindgren.Longstocking(a#13#0#0, a#13#1#0) } 
  Seq#Rank(a#13#0#0) < DtRank(#_module.Lindgren.Longstocking(a#13#0#0, a#13#1#0)));

function _module.Lindgren._h2(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#14#0#0: Seq Box, a#14#1#0: DatatypeType :: 
  { #_module.Lindgren.Longstocking(a#14#0#0, a#14#1#0) } 
  _module.Lindgren._h2(#_module.Lindgren.Longstocking(a#14#0#0, a#14#1#0))
     == a#14#1#0);

// Inductive rank
axiom (forall a#15#0#0: Seq Box, a#15#1#0: DatatypeType :: 
  { #_module.Lindgren.Longstocking(a#15#0#0, a#15#1#0) } 
  DtRank(a#15#1#0) < DtRank(#_module.Lindgren.Longstocking(a#15#0#0, a#15#1#0)));

// Constructor function declaration
function #_module.Lindgren.HerrNilsson() : DatatypeType;

const unique ##_module.Lindgren.HerrNilsson: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Lindgren.HerrNilsson())
   == ##_module.Lindgren.HerrNilsson;

function _module.Lindgren.HerrNilsson_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Lindgren.HerrNilsson_q(d) } 
  _module.Lindgren.HerrNilsson_q(d)
     <==> DatatypeCtorId(d) == ##_module.Lindgren.HerrNilsson);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Lindgren.HerrNilsson_q(d) } 
  _module.Lindgren.HerrNilsson_q(d) ==> d == #_module.Lindgren.HerrNilsson());

// Constructor $Is
axiom $Is(#_module.Lindgren.HerrNilsson(), Tclass._module.Lindgren());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.Lindgren.HerrNilsson(), Tclass._module.Lindgren(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Lindgren.HerrNilsson(), Tclass._module.Lindgren(), $h));

// Constructor literal
axiom #_module.Lindgren.HerrNilsson() == Lit(#_module.Lindgren.HerrNilsson());

// Depth-one case-split function
function $IsA#_module.Lindgren(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Lindgren(d) } 
  $IsA#_module.Lindgren(d)
     ==> _module.Lindgren.Pippi_q(d)
       || _module.Lindgren.Longstocking_q(d)
       || _module.Lindgren.HerrNilsson_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Lindgren.HerrNilsson_q(d), $Is(d, Tclass._module.Lindgren()) } 
    { _module.Lindgren.Longstocking_q(d), $Is(d, Tclass._module.Lindgren()) } 
    { _module.Lindgren.Pippi_q(d), $Is(d, Tclass._module.Lindgren()) } 
  $Is(d, Tclass._module.Lindgren())
     ==> _module.Lindgren.Pippi_q(d)
       || _module.Lindgren.Longstocking_q(d)
       || _module.Lindgren.HerrNilsson_q(d));

// Datatype extensional equality declaration
function _module.Lindgren#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Lindgren.Pippi
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Lindgren#Equal(a, b), _module.Lindgren.Pippi_q(a) } 
    { _module.Lindgren#Equal(a, b), _module.Lindgren.Pippi_q(b) } 
  _module.Lindgren.Pippi_q(a) && _module.Lindgren.Pippi_q(b)
     ==> (_module.Lindgren#Equal(a, b)
       <==> _module.Lindgren._h0(a) == _module.Lindgren._h0(b)));

// Datatype extensional equality definition: #_module.Lindgren.Longstocking
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Lindgren#Equal(a, b), _module.Lindgren.Longstocking_q(a) } 
    { _module.Lindgren#Equal(a, b), _module.Lindgren.Longstocking_q(b) } 
  _module.Lindgren.Longstocking_q(a) && _module.Lindgren.Longstocking_q(b)
     ==> (_module.Lindgren#Equal(a, b)
       <==> Seq#Equal(_module.Lindgren._h1(a), _module.Lindgren._h1(b))
         && _module.Lindgren#Equal(_module.Lindgren._h2(a), _module.Lindgren._h2(b))));

// Datatype extensional equality definition: #_module.Lindgren.HerrNilsson
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Lindgren#Equal(a, b), _module.Lindgren.HerrNilsson_q(a) } 
    { _module.Lindgren#Equal(a, b), _module.Lindgren.HerrNilsson_q(b) } 
  _module.Lindgren.HerrNilsson_q(a) && _module.Lindgren.HerrNilsson_q(b)
     ==> (_module.Lindgren#Equal(a, b) <==> true));

// Datatype extensionality axiom: _module.Lindgren
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Lindgren#Equal(a, b) } 
  _module.Lindgren#Equal(a, b) <==> a == b);

const unique class._module.Lindgren: ClassName;

const unique class._module.InitCalls?: ClassName;

function Tclass._module.InitCalls?() : Ty;

const unique Tagclass._module.InitCalls?: TyTag;

// Tclass._module.InitCalls? Tag
axiom Tag(Tclass._module.InitCalls?()) == Tagclass._module.InitCalls?
   && TagFamily(Tclass._module.InitCalls?()) == tytagFamily$InitCalls;

// Box/unbox axiom for Tclass._module.InitCalls?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.InitCalls?()) } 
  $IsBox(bx, Tclass._module.InitCalls?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.InitCalls?()));

// InitCalls: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.InitCalls?()) } 
  $Is($o, Tclass._module.InitCalls?())
     <==> $o == null || dtype($o) == Tclass._module.InitCalls?());

// InitCalls: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.InitCalls?(), $h) } 
  $IsAlloc($o, Tclass._module.InitCalls?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.InitCalls.z) == 0
   && FieldOfDecl(class._module.InitCalls?, field$z) == _module.InitCalls.z
   && !$IsGhostField(_module.InitCalls.z);

const _module.InitCalls.z: Field int;

// InitCalls.z: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.InitCalls.z) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.InitCalls?()
     ==> $Is(read($h, $o, _module.InitCalls.z), TInt));

// InitCalls.z: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.InitCalls.z) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.InitCalls?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.InitCalls.z), TInt, $h));

axiom FDim(_module.InitCalls.p) == 0
   && FieldOfDecl(class._module.InitCalls?, field$p) == _module.InitCalls.p
   && !$IsGhostField(_module.InitCalls.p);

const _module.InitCalls.p: Field ref;

// InitCalls.p: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.InitCalls.p) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.InitCalls?()
     ==> $Is(read($h, $o, _module.InitCalls.p), Tclass._module.InitCalls?()));

// InitCalls.p: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.InitCalls.p) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.InitCalls?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.InitCalls.p), Tclass._module.InitCalls?(), $h));

function Tclass._module.InitCalls() : Ty;

const unique Tagclass._module.InitCalls: TyTag;

// Tclass._module.InitCalls Tag
axiom Tag(Tclass._module.InitCalls()) == Tagclass._module.InitCalls
   && TagFamily(Tclass._module.InitCalls()) == tytagFamily$InitCalls;

// Box/unbox axiom for Tclass._module.InitCalls
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.InitCalls()) } 
  $IsBox(bx, Tclass._module.InitCalls())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.InitCalls()));

procedure CheckWellformed$$_module.InitCalls.Init(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap), 
    y#0: int);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.InitCalls.Init(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap), 
    y#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.InitCalls.z) == y#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.InitCalls.Init(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap), 
    y#0: int)
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.InitCalls.z) == y#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.InitCalls.Init(this: ref, y#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;

    // AddMethodImpl: Init, Impl$$_module.InitCalls.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(276,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(277,7)
    assume true;
    assert $_Frame[this, _module.InitCalls.z];
    assume true;
    $rhs#0 := y#0;
    $Heap := update($Heap, this, _module.InitCalls.z, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(277,10)"} true;
}



procedure CheckWellformed$$_module.InitCalls.InitFromReference(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.InitCalls())
         && $IsAlloc(q#0, Tclass._module.InitCalls(), $Heap));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.InitCalls.InitFromReference(this: ref, q#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: InitFromReference, CheckWellformed$$_module.InitCalls.InitFromReference
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(280,9): initial state"} true;
    assert q#0 != null;
    assume LitInt(15) <= read($Heap, q#0, _module.InitCalls.z);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(283,14): post-state"} true;
    assume read($Heap, this, _module.InitCalls.p) == q#0;
}



procedure Call$$_module.InitCalls.InitFromReference(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.InitCalls())
         && $IsAlloc(q#0, Tclass._module.InitCalls(), $Heap));
  // user-defined preconditions
  requires LitInt(15) <= read($Heap, q#0, _module.InitCalls.z);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.InitCalls.p) == q#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.InitCalls.InitFromReference(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap), 
    q#0: ref
       where $Is(q#0, Tclass._module.InitCalls())
         && $IsAlloc(q#0, Tclass._module.InitCalls(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(15) <= read($Heap, q#0, _module.InitCalls.z);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.InitCalls.p) == q#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.InitCalls.InitFromReference(this: ref, q#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.InitCalls?());

    // AddMethodImpl: InitFromReference, Impl$$_module.InitCalls.InitFromReference
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(284,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(285,7)
    assume true;
    assert $_Frame[this, _module.InitCalls.p];
    assume true;
    $rhs#0 := q#0;
    $Heap := update($Heap, this, _module.InitCalls.p, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(285,10)"} true;
}



procedure CheckWellformed$$_module.InitCalls.TestDriver(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.InitCalls.TestDriver(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.InitCalls.TestDriver(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.InitCalls())
         && $IsAlloc(this, Tclass._module.InitCalls(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.InitCalls.TestDriver(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#c#0: bool;
  var c#0: ref
     where defass#c#0
       ==> $Is(c#0, Tclass._module.InitCalls())
         && $IsAlloc(c#0, Tclass._module.InitCalls(), $Heap);
  var $nw: ref;
  var y##0: int;
  var d#0: ref
     where $Is(d#0, Tclass._module.InitCalls())
       && $IsAlloc(d#0, Tclass._module.InitCalls(), $Heap);
  var y##1: int;
  var e#0: ref
     where $Is(e#0, Tclass._module.InitCalls())
       && $IsAlloc(e#0, Tclass._module.InitCalls(), $Heap);
  var y##2: int;
  var f#0: ref
     where $Is(f#0, Tclass._System.object())
       && $IsAlloc(f#0, Tclass._System.object(), $Heap);
  var y##3: int;
  var g#Z#0: ref;
  var let#0#0#0: ref;
  var g#Z#1: ref;
  var let#1#0#0: ref;
  var r#0: ref
     where $Is(r#0, Tclass._module.InitCalls())
       && $IsAlloc(r#0, Tclass._module.InitCalls(), $Heap);
  var q##0: ref;
  var q##1: ref;

    // AddMethodImpl: TestDriver, Impl$$_module.InitCalls.TestDriver
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(289,2): initial state"} true;
    $_reverifyPost := false;
    havoc c#0 /* where defass#c#0
       ==> $Is(c#0, Tclass._module.InitCalls())
         && $IsAlloc(c#0, Tclass._module.InitCalls(), $Heap) */;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(291,7)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.InitCalls?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(291,24)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := LitInt(15);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.InitCalls.Init($nw, y##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(291,31)"} true;
    c#0 := $nw;
    defass#c#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(291,31)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(292,11)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.InitCalls?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(292,28)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##1 := LitInt(17);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.InitCalls.Init($nw, y##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(292,35)"} true;
    d#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(292,35)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(293,22)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.InitCalls?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(293,39)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##2 := LitInt(18);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.InitCalls.Init($nw, y##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(293,46)"} true;
    e#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(293,46)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(294,19)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.InitCalls?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(294,36)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##3 := LitInt(19);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.InitCalls.Init($nw, y##3);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(294,43)"} true;
    f#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(294,43)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(295,5)
    assert defass#c#0;
    assert {:subsumption 0} c#0 != null;
    assert {:subsumption 0} d#0 != null;
    assert {:subsumption 0} e#0 != null;
    assume true;
    assert read($Heap, c#0, _module.InitCalls.z)
         + read($Heap, d#0, _module.InitCalls.z)
         + read($Heap, e#0, _module.InitCalls.z)
       == LitInt(50);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(297,5)
    havoc g#Z#0;
    assume $Is(g#Z#0, Tclass._module.InitCalls());
    assert $Is(f#0, Tclass._module.InitCalls());
    assume let#0#0#0 == f#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.InitCalls());
    assume g#Z#0 == let#0#0#0;
    assume true;
    assert (var g#0 := f#0; f#0 == g#0);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(298,5)
    havoc g#Z#1;
    assume $Is(g#Z#1, Tclass._module.InitCalls());
    assert $Is(f#0, Tclass._module.InitCalls());
    assume let#1#0#0 == f#0;
    assume true;
    // CheckWellformedWithResult: any expression
    assume $Is(let#1#0#0, Tclass._module.InitCalls());
    assume g#Z#1 == let#1#0#0;
    assert {:subsumption 0} g#Z#1 != null;
    assume true;
    assert (var g#1 := f#0; read($Heap, g#1, _module.InitCalls.z) == LitInt(19));
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(301,11)
    assume true;
    assert defass#c#0;
    assume true;
    r#0 := c#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(301,14)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(302,7)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.InitCalls?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(302,24)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    q##0 := r#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.InitCalls.InitFromReference($nw, q##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(302,43)"} true;
    r#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(302,43)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(303,7)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.InitCalls?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(303,24)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    q##1 := r#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == $nw ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.InitCalls.InitFromReference($nw, q##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(303,43)"} true;
    r#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(303,43)"} true;
}



// _module.InitCalls: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.InitCalls()) } 
  $Is(c#0, Tclass._module.InitCalls())
     <==> $Is(c#0, Tclass._module.InitCalls?()) && c#0 != null);

// _module.InitCalls: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.InitCalls(), $h) } 
  $IsAlloc(c#0, Tclass._module.InitCalls(), $h)
     <==> $IsAlloc(c#0, Tclass._module.InitCalls?(), $h));

const unique class._module.SomeType?: ClassName;

function Tclass._module.SomeType?() : Ty;

const unique Tagclass._module.SomeType?: TyTag;

// Tclass._module.SomeType? Tag
axiom Tag(Tclass._module.SomeType?()) == Tagclass._module.SomeType?
   && TagFamily(Tclass._module.SomeType?()) == tytagFamily$SomeType;

// Box/unbox axiom for Tclass._module.SomeType?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SomeType?()) } 
  $IsBox(bx, Tclass._module.SomeType?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.SomeType?()));

// SomeType: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.SomeType?()) } 
  $Is($o, Tclass._module.SomeType?())
     <==> $o == null || dtype($o) == Tclass._module.SomeType?());

// SomeType: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.SomeType?(), $h) } 
  $IsAlloc($o, Tclass._module.SomeType?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.SomeType.x) == 0
   && FieldOfDecl(class._module.SomeType?, field$x) == _module.SomeType.x
   && !$IsGhostField(_module.SomeType.x);

const _module.SomeType.x: Field int;

// SomeType.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.SomeType.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.SomeType?()
     ==> $Is(read($h, $o, _module.SomeType.x), TInt));

// SomeType.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.SomeType.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.SomeType?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.SomeType.x), TInt, $h));

function Tclass._module.SomeType() : Ty;

const unique Tagclass._module.SomeType: TyTag;

// Tclass._module.SomeType Tag
axiom Tag(Tclass._module.SomeType()) == Tagclass._module.SomeType
   && TagFamily(Tclass._module.SomeType()) == tytagFamily$SomeType;

// Box/unbox axiom for Tclass._module.SomeType
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SomeType()) } 
  $IsBox(bx, Tclass._module.SomeType())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.SomeType()));

procedure CheckWellformed$$_module.SomeType.DoIt(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SomeType())
         && $IsAlloc(this, Tclass._module.SomeType(), $Heap), 
    stack#0: Seq Box
       where $Is(stack#0, TSeq(Tclass._module.SomeType()))
         && $IsAlloc(stack#0, TSeq(Tclass._module.SomeType()), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.SomeType.DoIt(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SomeType())
         && $IsAlloc(this, Tclass._module.SomeType(), $Heap), 
    stack#0: Seq Box
       where $Is(stack#0, TSeq(Tclass._module.SomeType()))
         && $IsAlloc(stack#0, TSeq(Tclass._module.SomeType()), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || (exists $i: int :: 
          0 <= $i && $i < Seq#Length(stack#0) && Seq#Index(stack#0, $i) == $Box($o)));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SomeType.DoIt(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SomeType())
         && $IsAlloc(this, Tclass._module.SomeType(), $Heap), 
    stack#0: Seq Box
       where $Is(stack#0, TSeq(Tclass._module.SomeType()))
         && $IsAlloc(stack#0, TSeq(Tclass._module.SomeType()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || (exists $i: int :: 
          0 <= $i && $i < Seq#Length(stack#0) && Seq#Index(stack#0, $i) == $Box($o)));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SomeType.DoIt(this: ref, stack#0: Seq Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref;
  var n#1: ref;
  var $prevHeap: Heap;

    // AddMethodImpl: DoIt, Impl$$_module.SomeType.DoIt
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (exists $i: int :: 
          0 <= $i && $i < Seq#Length(stack#0) && Seq#Index(stack#0, $i) == $Box($o)));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(358,2): initial state"} true;
    $_reverifyPost := false;
    // ----- forall statement (assign) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(359,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc n#0;
        assume $Is(n#0, Tclass._module.SomeType());
        assume true;
        assume Seq#Contains(stack#0, $Box(n#0));
        assert {:subsumption 0} n#0 != null;
        assume true;
        assert $_Frame[n#0, _module.SomeType.x];
        assume true;
        havoc n#1;
        assume $Is(n#1, Tclass._module.SomeType());
        assume Seq#Contains(stack#0, $Box(n#1));
        assume n#0 != n#1;
        assert n#0 != n#1
           || _module.SomeType.x != _module.SomeType.x
           || LitInt(10) == LitInt(10);
        assume false;
    }
    else
    {
        $prevHeap := $Heap;
        havoc $Heap;
        assume $HeapSucc($prevHeap, $Heap);
        assume (forall<alpha> $o: ref, $f: Field alpha :: 
          { read($Heap, $o, $f) } 
          read($Heap, $o, $f) == read($prevHeap, $o, $f)
             || (exists n#2: ref :: 
              $Is(n#2, Tclass._module.SomeType())
                 && Seq#Contains(stack#0, $Box(n#2))
                 && $o == n#2
                 && $f == _module.SomeType.x));
        assume (forall n#inv#0: ref :: 
          { read($Heap, n#inv#0, _module.SomeType.x) } 
          $Is(n#inv#0, Tclass._module.SomeType())
               && 
              n#inv#0 != null
               && Seq#Contains(stack#0, $Box(n#inv#0))
             ==> read($Heap, n#inv#0, _module.SomeType.x) == LitInt(10));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(361,4)"} true;
}



// _module.SomeType: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.SomeType()) } 
  $Is(c#0, Tclass._module.SomeType())
     <==> $Is(c#0, Tclass._module.SomeType?()) && c#0 != null);

// _module.SomeType: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.SomeType(), $h) } 
  $IsAlloc(c#0, Tclass._module.SomeType(), $h)
     <==> $IsAlloc(c#0, Tclass._module.SomeType?(), $h));

const unique class._module.Test?: ClassName;

function Tclass._module.Test?() : Ty;

const unique Tagclass._module.Test?: TyTag;

// Tclass._module.Test? Tag
axiom Tag(Tclass._module.Test?()) == Tagclass._module.Test?
   && TagFamily(Tclass._module.Test?()) == tytagFamily$Test;

// Box/unbox axiom for Tclass._module.Test?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Test?()) } 
  $IsBox(bx, Tclass._module.Test?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Test?()));

// Test: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Test?()) } 
  $Is($o, Tclass._module.Test?())
     <==> $o == null || dtype($o) == Tclass._module.Test?());

// Test: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Test?(), $h) } 
  $IsAlloc($o, Tclass._module.Test?(), $h) <==> $o == null || read($h, $o, alloc));

function Tclass._module.Test() : Ty;

const unique Tagclass._module.Test: TyTag;

// Tclass._module.Test Tag
axiom Tag(Tclass._module.Test()) == Tagclass._module.Test
   && TagFamily(Tclass._module.Test()) == tytagFamily$Test;

// Box/unbox axiom for Tclass._module.Test
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Test()) } 
  $IsBox(bx, Tclass._module.Test())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Test()));

procedure CheckWellformed$$_module.Test.test0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  free requires 62 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Test.test0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Test.test0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 62 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Test.test0(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: test0, Impl$$_module.Test.test0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(407,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(408,5)
    assume true;
    assert false;
}



procedure {:verify false} CheckWellformed$$_module.Test.test1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  free requires 63 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verify false} Call$$_module.Test.test1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verify false} Impl$$_module.Test.test1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 63 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verify false} Impl$$_module.Test.test1(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: test1, Impl$$_module.Test.test1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(412,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(413,5)
    assume true;
    assert false;
}



procedure CheckWellformed$$_module.Test.init0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  free requires 64 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Test.init0()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Test.init0()
   returns (this: ref where this != null && $Is(this, Tclass._module.Test()), 
    $_reverifyPost: bool);
  free requires 64 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Test.init0() returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: init0, Impl$$_module.Test.init0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(417,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(417,3)
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(418,5)
    assume true;
    assert false;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(417,3)
    assume !read($Heap, this, alloc);
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(417,3)
}



procedure {:verify false} CheckWellformed$$_module.Test.init1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  free requires 65 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verify false} Call$$_module.Test.init1()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verify false} Impl$$_module.Test.init1()
   returns (this: ref where this != null && $Is(this, Tclass._module.Test()), 
    $_reverifyPost: bool);
  free requires 65 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verify false} Impl$$_module.Test.init1() returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: init1, Impl$$_module.Test.init1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(422,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(422,3)
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(423,5)
    assume true;
    assert false;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(422,3)
    assume !read($Heap, this, alloc);
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(422,3)
}



// function declaration for _module.Test.test2
function _module.Test.test2($ly: LayerType, this: ref) : bool;

function _module.Test.test2#canCall(this: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: ref :: 
  { _module.Test.test2($LS($ly), this) } 
  _module.Test.test2($LS($ly), this) == _module.Test.test2($ly, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: ref :: 
  { _module.Test.test2(AsFuelBottom($ly), this) } 
  _module.Test.test2($ly, this) == _module.Test.test2($LZ, this));

// consequence axiom for _module.Test.test2
axiom 39 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref :: 
    { _module.Test.test2($ly, this) } 
    _module.Test.test2#canCall(this)
         || (39 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.Test()))
       ==> true);

function _module.Test.test2#requires(LayerType, ref) : bool;

// #requires axiom for _module.Test.test2
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Test.test2#requires($ly, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Test())
       && $IsAlloc(this, Tclass._module.Test(), $Heap)
     ==> _module.Test.test2#requires($ly, this) == true);

// definition axiom for _module.Test.test2 (revealed)
axiom 39 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Test.test2($LS($ly), this), $IsGoodHeap($Heap) } 
    _module.Test.test2#canCall(this)
         || (39 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Test())
           && $IsAlloc(this, Tclass._module.Test(), $Heap))
       ==> _module.Test.test2#canCall(this)
         && _module.Test.test2($LS($ly), this) == !Lit(_module.Test.test2($ly, this)));

// definition axiom for _module.Test.test2 for all literals (revealed)
axiom 39 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    {:weight 3} { _module.Test.test2($LS($ly), Lit(this)), $IsGoodHeap($Heap) } 
    _module.Test.test2#canCall(Lit(this))
         || (39 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Test())
           && $IsAlloc(this, Tclass._module.Test(), $Heap))
       ==> _module.Test.test2#canCall(Lit(this))
         && _module.Test.test2($LS($ly), Lit(this))
           == !Lit(_module.Test.test2($LS($ly), Lit(this))));

procedure CheckWellformed$$_module.Test.test2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Test.test2(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function test2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(426,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert false;
        assume _module.Test.test2#canCall(this);
        assume _module.Test.test2($LS($LZ), this) == !Lit(_module.Test.test2($LS($LZ), this));
        assume _module.Test.test2#canCall(this);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Test.test2($LS($LZ), this), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module.Test.test3
function _module.Test.test3($ly: LayerType, this: ref) : bool;

function _module.Test.test3#canCall(this: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: ref :: 
  { _module.Test.test3($LS($ly), this) } 
  _module.Test.test3($LS($ly), this) == _module.Test.test3($ly, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: ref :: 
  { _module.Test.test3(AsFuelBottom($ly), this) } 
  _module.Test.test3($ly, this) == _module.Test.test3($LZ, this));

// consequence axiom for _module.Test.test3
axiom 40 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref :: 
    { _module.Test.test3($ly, this) } 
    _module.Test.test3#canCall(this)
         || (40 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.Test()))
       ==> true);

function _module.Test.test3#requires(LayerType, ref) : bool;

// #requires axiom for _module.Test.test3
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { _module.Test.test3#requires($ly, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Test())
       && $IsAlloc(this, Tclass._module.Test(), $Heap)
     ==> _module.Test.test3#requires($ly, this) == true);

// definition axiom for _module.Test.test3 (revealed)
axiom 40 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { _module.Test.test3($LS($ly), this), $IsGoodHeap($Heap) } 
    _module.Test.test3#canCall(this)
         || (40 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Test())
           && $IsAlloc(this, Tclass._module.Test(), $Heap))
       ==> _module.Test.test3#canCall(this)
         && _module.Test.test3($LS($ly), this) == !Lit(_module.Test.test3($ly, this)));

// definition axiom for _module.Test.test3 for all literals (revealed)
axiom 40 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    {:weight 3} { _module.Test.test3($LS($ly), Lit(this)), $IsGoodHeap($Heap) } 
    _module.Test.test3#canCall(Lit(this))
         || (40 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Test())
           && $IsAlloc(this, Tclass._module.Test(), $Heap))
       ==> _module.Test.test3#canCall(Lit(this))
         && _module.Test.test3($LS($ly), Lit(this))
           == !Lit(_module.Test.test3($LS($ly), Lit(this))));

procedure {:verify false} CheckWellformed$$_module.Test.test3(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Test())
         && $IsAlloc(this, Tclass._module.Test(), $Heap));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verify false} CheckWellformed$$_module.Test.test3(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function test3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(431,27): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert false;
        assume _module.Test.test3#canCall(this);
        assume _module.Test.test3($LS($LZ), this) == !Lit(_module.Test.test3($LS($LZ), this));
        assume _module.Test.test3#canCall(this);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.Test.test3($LS($LZ), this), TBool);
        assert b$reqreads#0;
    }
}



// _module.Test: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Test()) } 
  $Is(c#0, Tclass._module.Test())
     <==> $Is(c#0, Tclass._module.Test?()) && c#0 != null);

// _module.Test: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Test(), $h) } 
  $IsAlloc(c#0, Tclass._module.Test(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Test?(), $h));

const unique class._module.AttributeTests?: ClassName;

function Tclass._module.AttributeTests?() : Ty;

const unique Tagclass._module.AttributeTests?: TyTag;

// Tclass._module.AttributeTests? Tag
axiom Tag(Tclass._module.AttributeTests?()) == Tagclass._module.AttributeTests?
   && TagFamily(Tclass._module.AttributeTests?()) == tytagFamily$AttributeTests;

// Box/unbox axiom for Tclass._module.AttributeTests?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AttributeTests?()) } 
  $IsBox(bx, Tclass._module.AttributeTests?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AttributeTests?()));

// AttributeTests: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.AttributeTests?()) } 
  $Is($o, Tclass._module.AttributeTests?())
     <==> $o == null || dtype($o) == Tclass._module.AttributeTests?());

// AttributeTests: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.AttributeTests?(), $h) } 
  $IsAlloc($o, Tclass._module.AttributeTests?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.AttributeTests.f) == 0
   && FieldOfDecl(class._module.AttributeTests?, field$f) == _module.AttributeTests.f
   && !$IsGhostField(_module.AttributeTests.f);

const _module.AttributeTests.f: Field int;

// AttributeTests.f: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.AttributeTests.f) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.AttributeTests?()
     ==> $Is(read($h, $o, _module.AttributeTests.f), TInt));

// AttributeTests.f: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.AttributeTests.f) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.AttributeTests?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.AttributeTests.f), TInt, $h));

function Tclass._module.AttributeTests() : Ty;

const unique Tagclass._module.AttributeTests: TyTag;

// Tclass._module.AttributeTests Tag
axiom Tag(Tclass._module.AttributeTests()) == Tagclass._module.AttributeTests
   && TagFamily(Tclass._module.AttributeTests()) == tytagFamily$AttributeTests;

// Box/unbox axiom for Tclass._module.AttributeTests
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.AttributeTests()) } 
  $IsBox(bx, Tclass._module.AttributeTests())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.AttributeTests()));

procedure CheckWellformed$$_module.AttributeTests.m0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AttributeTests.m0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AttributeTests.m0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.AttributeTests.m1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap))
   returns (r#0: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AttributeTests.m1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap))
   returns (r#0: bool);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AttributeTests.m1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap))
   returns (r#0: bool, $_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.AttributeTests.m2
function _module.AttributeTests.m2(this: ref) : bool;

function _module.AttributeTests.m2#canCall(this: ref) : bool;

// consequence axiom for _module.AttributeTests.m2
axiom 21 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    { _module.AttributeTests.m2(this) } 
    _module.AttributeTests.m2#canCall(this)
         || (21 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.AttributeTests()))
       ==> true);

function _module.AttributeTests.m2#requires(ref) : bool;

// #requires axiom for _module.AttributeTests.m2
axiom (forall this: ref :: 
  { _module.AttributeTests.m2#requires(this) } 
  this != null && $Is(this, Tclass._module.AttributeTests())
     ==> _module.AttributeTests.m2#requires(this) == true);

// definition axiom for _module.AttributeTests.m2 (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    { _module.AttributeTests.m2(this) } 
    _module.AttributeTests.m2#canCall(this)
         || (21 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.AttributeTests()))
       ==> _module.AttributeTests.m2(this) == Lit(true));

// definition axiom for _module.AttributeTests.m2 for all literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    {:weight 3} { _module.AttributeTests.m2(Lit(this)) } 
    _module.AttributeTests.m2#canCall(Lit(this))
         || (21 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.AttributeTests()))
       ==> _module.AttributeTests.m2(Lit(this)) == Lit(true));

procedure CheckWellformed$$_module.AttributeTests.m2(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.AttributeTests.C(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.AttributeTests.C()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AttributeTests.C()
   returns (this: ref where this != null && $Is(this, Tclass._module.AttributeTests()), 
    $_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.AttributeTests.testAttributes0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.AttributeTests())
         && $IsAlloc(r#0, Tclass._module.AttributeTests(), $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.AttributeTests.testAttributes0(this: ref) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: testAttributes0, CheckWellformed$$_module.AttributeTests.testAttributes0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || $o == this
           || $o == this
           || $o == this
           || $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(473,9): initial state"} true;
    assert this != null;
    assert this != null;
    assert this != null;
    assert this != null;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || 
          $o == this
           || $o == this
           || $o == this
           || $o == this
           || $o == this
           || $o == this
           || $o == this
           || $o == this);
    assume (forall<alpha> $o: ref, $f: Field alpha :: 
      { read($Heap, $o, $f) } 
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
           || 
          ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || $o == this
           || $o == this
           || $o == this
           || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(474,29): post-state"} true;
    assume true;
    assume true;
    assume true;
    assume true;
}



procedure Call$$_module.AttributeTests.testAttributes0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass._module.AttributeTests())
         && $IsAlloc(r#0, Tclass._module.AttributeTests(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Lit(true);
  free ensures true;
  ensures Lit(true);
  free ensures true;
  ensures Lit(true);
  free ensures true;
  ensures Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || $o == this
         || $o == this
         || $o == this
         || $o == this
         || $o == this
         || $o == this
         || $o == this);
  // frame condition: field granularity
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || 
        ($o == this && $f == _module.AttributeTests.f)
         || ($o == this && $f == _module.AttributeTests.f)
         || ($o == this && $f == _module.AttributeTests.f)
         || ($o == this && $f == _module.AttributeTests.f)
         || $o == this
         || $o == this
         || $o == this
         || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.AttributeTests.testAttributes0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.AttributeTests())
         && $IsAlloc(this, Tclass._module.AttributeTests(), $Heap))
   returns (defass#r#0: bool, 
    r#0: ref
       where defass#r#0
         ==> $Is(r#0, Tclass._module.AttributeTests())
           && $IsAlloc(r#0, Tclass._module.AttributeTests(), $Heap), 
    $_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Lit(true);
  free ensures true;
  ensures Lit(true);
  free ensures true;
  ensures Lit(true);
  free ensures true;
  ensures Lit(true);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || $o == this
         || $o == this
         || $o == this
         || $o == this
         || $o == this
         || $o == this
         || $o == this);
  // frame condition: field granularity
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f)
         || 
        ($o == this && $f == _module.AttributeTests.f)
         || ($o == this && $f == _module.AttributeTests.f)
         || ($o == this && $f == _module.AttributeTests.f)
         || ($o == this && $f == _module.AttributeTests.f)
         || $o == this
         || $o == this
         || $o == this
         || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.AttributeTests.testAttributes0(this: ref) returns (defass#r#0: bool, r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $PreLoopHeap$loop#0: Heap;
  var $Frame$loop#0: <beta>[ref,Field beta]bool;
  var preLoop$loop#0$defass#r#0: bool;
  var $decr_init$loop#00: int;
  var $decr_init$loop#01: int;
  var $decr_init$loop#02: int;
  var $decr_init$loop#03: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $decr$loop#01: int;
  var $decr$loop#02: int;
  var $decr$loop#03: int;
  var b1#0: bool;
  var $rhs##0: bool;
  var $rhs##1: bool;
  var $rhs##2: bool;
  var $rhs##3: bool;
  var b2#0: bool;
  var b2'#0: bool;
  var $rhs#0: bool;
  var $rhs#1: bool;
  var $rhs#2: bool;
  var $rhs#3: bool;
  var $rhs#4: bool;
  var $rhs#5: bool;
  var $rhs#6: bool;
  var $rhs#7: bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.AttributeTests())
       && $IsAlloc(c#0, Tclass._module.AttributeTests(), $Heap);
  var $nw: ref;
  var y#0: bool;
  var x#0: real;
  var aa#0: ref
     where $Is(aa#0, Tclass._System.array(TReal))
       && $IsAlloc(aa#0, Tclass._System.array(TReal), $Heap);
  var y#1: int;
  var x#1: int;
  var z#0: bool;

    // AddMethodImpl: testAttributes0, Impl$$_module.AttributeTests.testAttributes0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || $o == this
           || $o == this
           || $o == this
           || $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(490,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(491,5)
    assume true;
    assert {:boolAttr true} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(492,5)
    assume true;
    assert {:boolAttr false} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(493,5)
    assume true;
    assert {:intAttr 0} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(494,5)
    assume true;
    assert {:intAttr 1} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(496,5)
    // Assume Fuel Constant
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && (
            ($o == this && $f == _module.AttributeTests.f)
             || ($o == this && $f == _module.AttributeTests.f)
             || ($o == this && $f == _module.AttributeTests.f)
             || ($o == this && $f == _module.AttributeTests.f))
         ==> $_Frame[$o, $f]);
    $Frame$loop#0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f)
           || ($o == this && $f == _module.AttributeTests.f));
    $PreLoopHeap$loop#0 := $Heap;
    preLoop$loop#0$defass#r#0 := defass#r#0;
    $decr_init$loop#00 := read($Heap, this, _module.AttributeTests.f);
    $decr_init$loop#01 := read($Heap, this, _module.AttributeTests.f);
    $decr_init$loop#02 := read($Heap, this, _module.AttributeTests.f);
    $decr_init$loop#03 := read($Heap, this, _module.AttributeTests.f);
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Lit(true);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Lit(true);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Lit(true);
      free invariant $w$loop#0 ==> true;
      invariant $w$loop#0 ==> Lit(true);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]
             || 
            $o == this
             || $o == this
             || $o == this
             || $o == this
             || $o == this
             || $o == this
             || $o == this
             || $o == this);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
             || 
            ($o == this && $f == _module.AttributeTests.f)
             || ($o == this && $f == _module.AttributeTests.f)
             || ($o == this && $f == _module.AttributeTests.f)
             || ($o == this && $f == _module.AttributeTests.f)
             || $o == this
             || $o == this
             || $o == this
             || $o == this);
      free invariant $HeapSuccGhost($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f)
             || $Frame$loop#0[$o, $f]);
      free invariant preLoop$loop#0$defass#r#0 ==> defass#r#0;
      free invariant read($Heap, this, _module.AttributeTests.f) <= $decr_init$loop#00
         && (read($Heap, this, _module.AttributeTests.f) == $decr_init$loop#00
           ==> read($Heap, this, _module.AttributeTests.f) <= $decr_init$loop#01
             && (read($Heap, this, _module.AttributeTests.f) == $decr_init$loop#01
               ==> read($Heap, this, _module.AttributeTests.f) <= $decr_init$loop#02
                 && (read($Heap, this, _module.AttributeTests.f) == $decr_init$loop#02
                   ==> read($Heap, this, _module.AttributeTests.f) <= $decr_init$loop#03
                     && (read($Heap, this, _module.AttributeTests.f) == $decr_init$loop#03 ==> true))));
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(496,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(false))
        {
            break;
        }

        $decr$loop#00 := read($Heap, this, _module.AttributeTests.f);
        $decr$loop#01 := read($Heap, this, _module.AttributeTests.f);
        $decr$loop#02 := read($Heap, this, _module.AttributeTests.f);
        $decr$loop#03 := read($Heap, this, _module.AttributeTests.f);
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(496,5)
        assert 0 <= $decr$loop#00
           || read($Heap, this, _module.AttributeTests.f) == $decr$loop#00;
        assert 0 <= $decr$loop#01
           || read($Heap, this, _module.AttributeTests.f) < $decr$loop#00
           || read($Heap, this, _module.AttributeTests.f) == $decr$loop#01;
        assert 0 <= $decr$loop#02
           || read($Heap, this, _module.AttributeTests.f) < $decr$loop#00
           || read($Heap, this, _module.AttributeTests.f) < $decr$loop#01
           || read($Heap, this, _module.AttributeTests.f) == $decr$loop#02;
        assert 0 <= $decr$loop#03
           || read($Heap, this, _module.AttributeTests.f) < $decr$loop#00
           || read($Heap, this, _module.AttributeTests.f) < $decr$loop#01
           || read($Heap, this, _module.AttributeTests.f) < $decr$loop#02
           || read($Heap, this, _module.AttributeTests.f) == $decr$loop#03;
        assert read($Heap, this, _module.AttributeTests.f) < $decr$loop#00
           || (read($Heap, this, _module.AttributeTests.f) == $decr$loop#00
             && (read($Heap, this, _module.AttributeTests.f) < $decr$loop#01
               || (read($Heap, this, _module.AttributeTests.f) == $decr$loop#01
                 && (read($Heap, this, _module.AttributeTests.f) < $decr$loop#02
                   || (read($Heap, this, _module.AttributeTests.f) == $decr$loop#02
                     && read($Heap, this, _module.AttributeTests.f) < $decr$loop#03)))));
        assume true;
        assume true;
        assume true;
        assume true;
    }

    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(513,7)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AttributeTests.m0(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(513,25)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(514,7)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AttributeTests.m0(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(514,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(515,7)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AttributeTests.m0(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(515,21)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(516,7)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AttributeTests.m0(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(516,21)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(518,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AttributeTests.m0(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(518,30)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(519,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AttributeTests.m0(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(519,31)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(520,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AttributeTests.m0(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(520,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(521,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.AttributeTests.m0(this);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(521,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(523,17)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.AttributeTests.m1(this);
    // TrCallStmt: After ProcessCallStmt
    b1#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(523,35)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(524,13)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$_module.AttributeTests.m1(this);
    // TrCallStmt: After ProcessCallStmt
    b1#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(524,32)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(525,13)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##2 := Call$$_module.AttributeTests.m1(this);
    // TrCallStmt: After ProcessCallStmt
    b1#0 := $rhs##2;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(525,27)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(526,13)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##3 := Call$$_module.AttributeTests.m1(this);
    // TrCallStmt: After ProcessCallStmt
    b1#0 := $rhs##3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(526,27)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(528,17)
    assume true;
    assume true;
    assume _module.AttributeTests.m2#canCall(this);
    assume _module.AttributeTests.m2#canCall(this);
    $rhs#0 := Lit(_module.AttributeTests.m2(this));
    assume _module.AttributeTests.m2#canCall(this);
    assume _module.AttributeTests.m2#canCall(this);
    $rhs#1 := Lit(_module.AttributeTests.m2(this));
    b2#0 := $rhs#0;
    b2'#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(528,63)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(529,13)
    assume true;
    assume true;
    assume _module.AttributeTests.m2#canCall(this);
    assume _module.AttributeTests.m2#canCall(this);
    $rhs#2 := Lit(_module.AttributeTests.m2(this));
    assume _module.AttributeTests.m2#canCall(this);
    assume _module.AttributeTests.m2#canCall(this);
    $rhs#3 := Lit(_module.AttributeTests.m2(this));
    b2#0 := $rhs#2;
    b2'#0 := $rhs#3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(529,61)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(530,13)
    assume true;
    assume true;
    assume _module.AttributeTests.m2#canCall(this);
    assume _module.AttributeTests.m2#canCall(this);
    $rhs#4 := Lit(_module.AttributeTests.m2(this));
    assume _module.AttributeTests.m2#canCall(this);
    assume _module.AttributeTests.m2#canCall(this);
    $rhs#5 := Lit(_module.AttributeTests.m2(this));
    b2#0 := $rhs#4;
    b2'#0 := $rhs#5;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(530,56)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(531,13)
    assume true;
    assume true;
    assume _module.AttributeTests.m2#canCall(this);
    assume _module.AttributeTests.m2#canCall(this);
    $rhs#6 := Lit(_module.AttributeTests.m2(this));
    assume _module.AttributeTests.m2#canCall(this);
    assume _module.AttributeTests.m2#canCall(this);
    $rhs#7 := Lit(_module.AttributeTests.m2(this));
    b2#0 := $rhs#6;
    b2'#0 := $rhs#7;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(531,56)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(533,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(533,33)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.AttributeTests.C();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(533,52)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(533,52)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(534,7)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(534,29)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.AttributeTests.C();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(534,49)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(534,49)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(535,7)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(535,29)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.AttributeTests.C();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(535,44)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(535,44)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(536,7)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(536,29)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.AttributeTests.C();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(536,44)"} true;
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(536,44)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(538,5)
    if (*)
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(539,7)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(539,7)
        assume true;
        // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(539,33)
        // TrCallStmt: Before ProcessCallStmt
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $nw := Call$$_module.AttributeTests.C();
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(539,52)"} true;
        r#0 := $nw;
        defass#r#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(539,52)"} true;
        assert defass#r#0;
        return;
    }
    else
    {
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(541,7)
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(541,7)
        assume true;
        // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(541,33)
        // TrCallStmt: Before ProcessCallStmt
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $nw := Call$$_module.AttributeTests.C();
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(541,48)"} true;
        r#0 := $nw;
        defass#r#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(541,48)"} true;
        assert defass#r#0;
        return;
    }

    havoc y#0, x#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(547,12)
    assume true;
    assert 0 <= LitInt(120);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TReal);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(120);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    aa#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(547,27)"} true;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(548,5)
    if (*)
    {
        // Assume Fuel Constant
        havoc y#1, x#1, z#0;
        assume true;
        assume true;
        assume x#1 < y#1;
        assert z#0 && LitInt(0) <= x#1 && x#1 < _System.array.Length(aa#0)
           ==> $Unbox(read($Heap, aa#0, IndexField(x#1))): real == LitReal(0e0);
        assume false;
    }
    else
    {
        assume (forall y#2: int, x#2: int, z#1: bool :: 
          {:trgr x#2 == y#2} {:tri z#1 == z#1} 
          x#2 < y#2
             ==> 
            z#1 && LitInt(0) <= x#2 && x#2 < _System.array.Length(aa#0)
             ==> $Unbox(read($Heap, aa#0, IndexField(x#2))): real == LitReal(0e0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(551,4)"} true;
    assert defass#r#0;
}



// _module.AttributeTests: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.AttributeTests()) } 
  $Is(c#0, Tclass._module.AttributeTests())
     <==> $Is(c#0, Tclass._module.AttributeTests?()) && c#0 != null);

// _module.AttributeTests: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.AttributeTests(), $h) } 
  $IsAlloc(c#0, Tclass._module.AttributeTests(), $h)
     <==> $IsAlloc(c#0, Tclass._module.AttributeTests?(), $h));

// Constructor function declaration
function #_module.QuiteFinite.QQA() : DatatypeType;

const unique ##_module.QuiteFinite.QQA: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.QuiteFinite.QQA()) == ##_module.QuiteFinite.QQA;

function _module.QuiteFinite.QQA_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.QuiteFinite.QQA_q(d) } 
  _module.QuiteFinite.QQA_q(d) <==> DatatypeCtorId(d) == ##_module.QuiteFinite.QQA);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.QuiteFinite.QQA_q(d) } 
  _module.QuiteFinite.QQA_q(d) ==> d == #_module.QuiteFinite.QQA());

function Tclass._module.QuiteFinite() : Ty;

const unique Tagclass._module.QuiteFinite: TyTag;

// Tclass._module.QuiteFinite Tag
axiom Tag(Tclass._module.QuiteFinite()) == Tagclass._module.QuiteFinite
   && TagFamily(Tclass._module.QuiteFinite()) == tytagFamily$QuiteFinite;

// Box/unbox axiom for Tclass._module.QuiteFinite
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.QuiteFinite()) } 
  $IsBox(bx, Tclass._module.QuiteFinite())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.QuiteFinite()));

// Constructor $Is
axiom $Is(#_module.QuiteFinite.QQA(), Tclass._module.QuiteFinite());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.QuiteFinite.QQA(), Tclass._module.QuiteFinite(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.QuiteFinite.QQA(), Tclass._module.QuiteFinite(), $h));

// Constructor function declaration
function #_module.QuiteFinite.QQB() : DatatypeType;

const unique ##_module.QuiteFinite.QQB: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.QuiteFinite.QQB()) == ##_module.QuiteFinite.QQB;

function _module.QuiteFinite.QQB_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.QuiteFinite.QQB_q(d) } 
  _module.QuiteFinite.QQB_q(d) <==> DatatypeCtorId(d) == ##_module.QuiteFinite.QQB);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.QuiteFinite.QQB_q(d) } 
  _module.QuiteFinite.QQB_q(d) ==> d == #_module.QuiteFinite.QQB());

// Constructor $Is
axiom $Is(#_module.QuiteFinite.QQB(), Tclass._module.QuiteFinite());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.QuiteFinite.QQB(), Tclass._module.QuiteFinite(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.QuiteFinite.QQB(), Tclass._module.QuiteFinite(), $h));

// Constructor function declaration
function #_module.QuiteFinite.QQC() : DatatypeType;

const unique ##_module.QuiteFinite.QQC: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.QuiteFinite.QQC()) == ##_module.QuiteFinite.QQC;

function _module.QuiteFinite.QQC_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.QuiteFinite.QQC_q(d) } 
  _module.QuiteFinite.QQC_q(d) <==> DatatypeCtorId(d) == ##_module.QuiteFinite.QQC);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.QuiteFinite.QQC_q(d) } 
  _module.QuiteFinite.QQC_q(d) ==> d == #_module.QuiteFinite.QQC());

// Constructor $Is
axiom $Is(#_module.QuiteFinite.QQC(), Tclass._module.QuiteFinite());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.QuiteFinite.QQC(), Tclass._module.QuiteFinite(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.QuiteFinite.QQC(), Tclass._module.QuiteFinite(), $h));

// Depth-one case-split function
function $IsA#_module.QuiteFinite(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.QuiteFinite(d) } 
  $IsA#_module.QuiteFinite(d)
     ==> _module.QuiteFinite.QQA_q(d)
       || _module.QuiteFinite.QQB_q(d)
       || _module.QuiteFinite.QQC_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.QuiteFinite.QQC_q(d), $Is(d, Tclass._module.QuiteFinite()) } 
    { _module.QuiteFinite.QQB_q(d), $Is(d, Tclass._module.QuiteFinite()) } 
    { _module.QuiteFinite.QQA_q(d), $Is(d, Tclass._module.QuiteFinite()) } 
  $Is(d, Tclass._module.QuiteFinite())
     ==> _module.QuiteFinite.QQA_q(d)
       || _module.QuiteFinite.QQB_q(d)
       || _module.QuiteFinite.QQC_q(d));

function $Eq#_module.QuiteFinite(LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.QuiteFinite($LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.QuiteFinite()) && $Is(d1, Tclass._module.QuiteFinite())
     ==> ($Eq#_module.QuiteFinite($LS(ly), d0, d1)
       <==> (_module.QuiteFinite.QQA_q(d0) && _module.QuiteFinite.QQA_q(d1))
         || (_module.QuiteFinite.QQB_q(d0) && _module.QuiteFinite.QQB_q(d1))
         || (_module.QuiteFinite.QQC_q(d0) && _module.QuiteFinite.QQC_q(d1))));

// Unbump layer co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.QuiteFinite($LS(ly), d0, d1) } 
  $Eq#_module.QuiteFinite($LS(ly), d0, d1)
     <==> $Eq#_module.QuiteFinite(ly, d0, d1));

// Equality for codatatypes
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.QuiteFinite($LS(ly), d0, d1) } 
  $Eq#_module.QuiteFinite($LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.QuiteFinite(Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.QuiteFinite()) && $Is(d1, Tclass._module.QuiteFinite())
     ==> ($PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (_module.QuiteFinite.QQA_q(d0) && _module.QuiteFinite.QQA_q(d1))
             || (_module.QuiteFinite.QQB_q(d0) && _module.QuiteFinite.QQB_q(d1))
             || (_module.QuiteFinite.QQC_q(d0) && _module.QuiteFinite.QQC_q(d1)))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k) ==> $Eq#_module.QuiteFinite(ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.QuiteFinite(k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.QuiteFinite($LS(ly), d0, d1) } 
  $Eq#_module.QuiteFinite($LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.QuiteFinite($LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.QuiteFinite(ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k ==> $PrefixEq#_module.QuiteFinite(ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.QuiteFinite($LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType, m: Box :: 
  { $PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1), $PrefixEq#_module.QuiteFinite(m, $LS(ly), d0, d1) } 
  ORD#Less(k, m) && $PrefixEq#_module.QuiteFinite(m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1) } 
  d0 == d1 ==> $PrefixEq#_module.QuiteFinite(k, $LS(ly), d0, d1));

const unique class._module.QuiteFinite: ClassName;

const unique class._module.GT?: ClassName;

function Tclass._module.GT?() : Ty;

const unique Tagclass._module.GT?: TyTag;

// Tclass._module.GT? Tag
axiom Tag(Tclass._module.GT?()) == Tagclass._module.GT?
   && TagFamily(Tclass._module.GT?()) == tytagFamily$GT;

// Box/unbox axiom for Tclass._module.GT?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.GT?()) } 
  $IsBox(bx, Tclass._module.GT?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.GT?()));

// GT: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.GT?()) } 
  $Is($o, Tclass._module.GT?())
     <==> $o == null || dtype($o) == Tclass._module.GT?());

// GT: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.GT?(), $h) } 
  $IsAlloc($o, Tclass._module.GT?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.GT.x) == 0
   && FieldOfDecl(class._module.GT?, field$x) == _module.GT.x
   && !$IsGhostField(_module.GT.x);

const _module.GT.x: Field int;

// GT.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.GT.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.GT?()
     ==> $Is(read($h, $o, _module.GT.x), TInt));

// GT.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.GT.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.GT?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.GT.x), TInt, $h));

axiom FDim(_module.GT.y) == 0
   && FieldOfDecl(class._module.GT?, field$y) == _module.GT.y
   && !$IsGhostField(_module.GT.y);

const _module.GT.y: Field int;

// GT.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.GT.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.GT?()
     ==> $Is(read($h, $o, _module.GT.y), TInt));

// GT.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.GT.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.GT?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.GT.y), TInt, $h));

axiom FDim(_module.GT.z) == 0
   && FieldOfDecl(class._module.GT?, field$z) == _module.GT.z
   && $IsGhostField(_module.GT.z);

const _module.GT.z: Field int;

// GT.z: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.GT.z) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.GT?()
     ==> $Is(read($h, $o, _module.GT.z), TInt));

// GT.z: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.GT.z) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.GT?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.GT.z), TInt, $h));

function Tclass._module.GT() : Ty;

const unique Tagclass._module.GT: TyTag;

// Tclass._module.GT Tag
axiom Tag(Tclass._module.GT()) == Tagclass._module.GT
   && TagFamily(Tclass._module.GT()) == tytagFamily$GT;

// Box/unbox axiom for Tclass._module.GT
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.GT()) } 
  $IsBox(bx, Tclass._module.GT())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.GT()));

procedure CheckWellformed$$_module.GT.M0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap), 
    N#0: int);
  free requires 66 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.GT.M0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap), 
    N#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.GT.M0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap), 
    N#0: int)
   returns ($_reverifyPost: bool);
  free requires 66 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.GT.M0(this: ref, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $obj1: ref;
  var $rhs#0_0: int;
  var $rhs#0_1: int;

    // AddMethodImpl: M0, Impl$$_module.GT.M0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(727,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(728,7)
    assume true;
    assert $_Frame[this, _module.GT.x];
    assume true;
    $rhs#0 := LitInt(18);
    $Heap := update($Heap, this, _module.GT.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(728,11)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(729,11)
    assume true;
    assume true;
    n#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(729,14)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(730,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 100 - n#0;
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
      free invariant 100 - n#0 <= $decr_init$loop#00 && (100 - n#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(730,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= n#0)
        {
            break;
        }

        $decr$loop#00 := 100 - n#0;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(731,12)
        assume true;
        assume true;
        $obj1 := this;
        assert $_Frame[$obj1, _module.GT.y];
        assume true;
        $rhs#0_0 := n#0 + 1;
        assume true;
        $rhs#0_1 := read($Heap, this, _module.GT.y) + 1;
        n#0 := $rhs#0_0;
        $Heap := update($Heap, $obj1, _module.GT.y, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(731,26)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(730,5)
        assert 0 <= $decr$loop#00 || 100 - n#0 == $decr$loop#00;
        assert 100 - n#0 < $decr$loop#00;
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(733,5)
    assume true;
    assert read($Heap, this, _module.GT.x) == LitInt(18);
}



procedure CheckWellformed$$_module.GT.M1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap), 
    N#0: int);
  free requires 67 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.GT.M1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap), 
    N#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.GT.M1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap), 
    N#0: int)
   returns ($_reverifyPost: bool);
  free requires 67 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.GT.M1(this: ref, N#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: int;
  var n#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $obj1: ref;
  var $rhs#0_0: int;
  var $rhs#0_1: int;

    // AddMethodImpl: M1, Impl$$_module.GT.M1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(737,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(738,7)
    assume true;
    assert $_Frame[this, _module.GT.x];
    assume true;
    $rhs#0 := LitInt(18);
    $Heap := update($Heap, this, _module.GT.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(738,11)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(739,17)
    assume true;
    assume true;
    n#0 := N#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(739,20)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(740,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := 100 - n#0;
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || $o == this);
      free invariant $HeapSuccGhost($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant 100 - n#0 <= $decr_init$loop#00 && (100 - n#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(740,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (100 <= n#0)
        {
            break;
        }

        $decr$loop#00 := 100 - n#0;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(741,12)
        assume true;
        assume true;
        $obj1 := this;
        assert $_Frame[$obj1, _module.GT.z];
        assume true;
        $rhs#0_0 := n#0 + 1;
        assume true;
        $rhs#0_1 := read($Heap, this, _module.GT.z) + 1;
        n#0 := $rhs#0_0;
        $Heap := update($Heap, $obj1, _module.GT.z, $rhs#0_1);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(741,26)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(740,5)
        assert 0 <= $decr$loop#00 || 100 - n#0 == $decr$loop#00;
        assert 100 - n#0 < $decr$loop#00;
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(743,5)
    assume true;
    assert read($Heap, this, _module.GT.x) == LitInt(18);
}



procedure CheckWellformed$$_module.GT.P0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.GT.P0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.GT.P1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap));
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.GT.P1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSuccGhost(old($Heap), $Heap);



procedure CheckWellformed$$_module.GT.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap));
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.GT.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.GT.Q(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.GT())
         && $IsAlloc(this, Tclass._module.GT(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.GT.Q(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0_0: ref;
  var x#0: ref;

    // AddMethodImpl: Q, Impl$$_module.GT.Q
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(751,2): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(752,5)
    if (*)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(753,9)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.GT.P0(this);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(753,10)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(754,7)
        // Begin Comprehension WF check
        havoc x#0_0;
        if ($Is(x#0_0, Tclass._module.GT()))
        {
            if ($IsAlloc(x#0_0, Tclass._module.GT?(), $Heap))
            {
            }
        }

        // End Comprehension WF check
        assume true;
        assert (forall x#0_1: ref :: 
          {:nowarn} 
          $Is(x#0_1, Tclass._module.GT())
             ==> 
            $IsAlloc(x#0_1, Tclass._module.GT?(), $Heap)
             ==> $IsAlloc(x#0_1, Tclass._module.GT?(), old($Heap)));
    }
    else
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(756,9)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) && $o == this ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.GT.P1(this);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(756,10)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(757,7)
        // Begin Comprehension WF check
        havoc x#0;
        if ($Is(x#0, Tclass._module.GT()))
        {
            if ($IsAlloc(x#0, Tclass._module.GT?(), $Heap))
            {
            }
        }

        // End Comprehension WF check
        assume true;
        assert (forall x#1: ref :: 
          {:nowarn} 
          $Is(x#1, Tclass._module.GT())
             ==> 
            $IsAlloc(x#1, Tclass._module.GT?(), $Heap)
             ==> $IsAlloc(x#1, Tclass._module.GT?(), old($Heap)));
    }
}



// _module.GT: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.GT()) } 
  $Is(c#0, Tclass._module.GT()) <==> $Is(c#0, Tclass._module.GT?()) && c#0 != null);

// _module.GT: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.GT(), $h) } 
  $IsAlloc(c#0, Tclass._module.GT(), $h)
     <==> $IsAlloc(c#0, Tclass._module.GT?(), $h));

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

procedure CheckWellformed$$_module.__default.QuantifierRange0(_module._default.QuantifierRange0$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange0$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange0$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange0$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange0$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange0$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange0$T, $Heap), 
    N#0: int);
  free requires 68 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.QuantifierRange0(_module._default.QuantifierRange0$T: Ty, 
    a#0: Seq Box, 
    x#0: Box, 
    y#0: Box, 
    N#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var k#2: int;
  var k#3: int;
  var k#5: int;

    // AddMethodImpl: QuantifierRange0, CheckWellformed$$_module.__default.QuantifierRange0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(309,7): initial state"} true;
    if (LitInt(0) <= N#0)
    {
    }

    assume LitInt(0) <= N#0 && N#0 <= Seq#Length(a#0);
    havoc k#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= k#0;
        assume k#0 < N#0;
        assert 0 <= k#0 && k#0 < Seq#Length(a#0);
        assume Seq#Index(a#0, k#0) != x#0;
    }
    else
    {
        assume LitInt(0) <= k#0 && k#0 < N#0 ==> Seq#Index(a#0, k#0) != x#0;
    }

    assume (forall k#1: int :: 
      { Seq#Index(a#0, k#1) } 
      LitInt(0) <= k#1 && k#1 < N#0 ==> Seq#Index(a#0, k#1) != x#0);
    havoc k#2;
    assume true;
    assume LitInt(0) <= k#2;
    assume k#2 < N#0;
    assert 0 <= k#2 && k#2 < Seq#Length(a#0);
    assume Seq#Index(a#0, k#2) == y#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(313,10): post-state"} true;
    havoc k#3;
    assume true;
    if (*)
    {
        assume LitInt(0) <= k#3;
        assume k#3 < N#0;
        assert 0 <= k#3 && k#3 < Seq#Length(a#0);
        assume Seq#Index(a#0, k#3) != x#0;
    }
    else
    {
        assume LitInt(0) <= k#3 && k#3 < N#0 ==> Seq#Index(a#0, k#3) != x#0;
    }

    assume (forall k#4: int :: 
      { Seq#Index(a#0, k#4) } 
      true ==> LitInt(0) <= k#4 && k#4 < N#0 ==> Seq#Index(a#0, k#4) != x#0);
    havoc k#5;
    assume true;
    assume LitInt(0) <= k#5;
    assume k#5 < N#0;
    assert 0 <= k#5 && k#5 < Seq#Length(a#0);
    assume Seq#Index(a#0, k#5) == y#0;
}



procedure Call$$_module.__default.QuantifierRange0(_module._default.QuantifierRange0$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange0$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange0$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange0$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange0$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange0$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange0$T, $Heap), 
    N#0: int);
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  requires N#0 <= Seq#Length(a#0);
  requires (forall k#1: int :: 
    { Seq#Index(a#0, k#1) } 
    LitInt(0) <= k#1 && k#1 < N#0 ==> Seq#Index(a#0, k#1) != x#0);
  requires (exists k#6: int :: 
    { Seq#Index(a#0, k#6) } 
    LitInt(0) <= k#6 && k#6 < N#0 && Seq#Index(a#0, k#6) == y#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall k#4: int :: 
    { Seq#Index(a#0, k#4) } 
    true ==> LitInt(0) <= k#4 && k#4 < N#0 ==> Seq#Index(a#0, k#4) != x#0);
  free ensures true;
  ensures (exists k#7: int :: 
    { Seq#Index(a#0, k#7) } 
    LitInt(0) <= k#7 && k#7 < N#0 && Seq#Index(a#0, k#7) == y#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.QuantifierRange0(_module._default.QuantifierRange0$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange0$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange0$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange0$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange0$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange0$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange0$T, $Heap), 
    N#0: int)
   returns ($_reverifyPost: bool);
  free requires 68 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  requires N#0 <= Seq#Length(a#0);
  requires (forall k#1: int :: 
    { Seq#Index(a#0, k#1) } 
    LitInt(0) <= k#1 && k#1 < N#0 ==> Seq#Index(a#0, k#1) != x#0);
  requires (exists k#6: int :: 
    { Seq#Index(a#0, k#6) } 
    LitInt(0) <= k#6 && k#6 < N#0 && Seq#Index(a#0, k#6) == y#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall k#4: int :: 
    { Seq#Index(a#0, k#4) } 
    true ==> LitInt(0) <= k#4 && k#4 < N#0 ==> Seq#Index(a#0, k#4) != x#0);
  free ensures true;
  ensures (exists k#7: int :: 
    { Seq#Index(a#0, k#7) } 
    LitInt(0) <= k#7 && k#7 < N#0 && Seq#Index(a#0, k#7) == y#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.QuantifierRange0(_module._default.QuantifierRange0$T: Ty, 
    a#0: Seq Box, 
    x#0: Box, 
    y#0: Box, 
    N#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: QuantifierRange0, Impl$$_module.__default.QuantifierRange0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(315,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(316,3)
    assume true;
    assert x#0 != y#0;
}



procedure CheckWellformed$$_module.__default.QuantifierRange1(_module._default.QuantifierRange1$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange1$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange1$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange1$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange1$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange1$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange1$T, $Heap), 
    N#0: int);
  free requires 69 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.QuantifierRange1(_module._default.QuantifierRange1$T: Ty, 
    a#0: Seq Box, 
    x#0: Box, 
    y#0: Box, 
    N#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var k#2: int;
  var k#3: int;
  var k#5: int;

    // AddMethodImpl: QuantifierRange1, CheckWellformed$$_module.__default.QuantifierRange1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(319,7): initial state"} true;
    if (LitInt(0) <= N#0)
    {
    }

    assume LitInt(0) <= N#0 && N#0 <= Seq#Length(a#0);
    havoc k#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= k#0;
        assume k#0 < N#0;
        assert 0 <= k#0 && k#0 < Seq#Length(a#0);
        assume Seq#Index(a#0, k#0) != x#0;
    }
    else
    {
        assume LitInt(0) <= k#0 && k#0 < N#0 ==> Seq#Index(a#0, k#0) != x#0;
    }

    assume (forall k#1: int :: 
      { Seq#Index(a#0, k#1) } 
      true ==> LitInt(0) <= k#1 && k#1 < N#0 ==> Seq#Index(a#0, k#1) != x#0);
    havoc k#2;
    assume true;
    assume LitInt(0) <= k#2;
    assume k#2 < N#0;
    assert 0 <= k#2 && k#2 < Seq#Length(a#0);
    assume Seq#Index(a#0, k#2) == y#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(323,10): post-state"} true;
    havoc k#3;
    assume true;
    if (*)
    {
        assume LitInt(0) <= k#3;
        assume k#3 < N#0;
        assert 0 <= k#3 && k#3 < Seq#Length(a#0);
        assume Seq#Index(a#0, k#3) != x#0;
    }
    else
    {
        assume LitInt(0) <= k#3 && k#3 < N#0 ==> Seq#Index(a#0, k#3) != x#0;
    }

    assume (forall k#4: int :: 
      { Seq#Index(a#0, k#4) } 
      LitInt(0) <= k#4 && k#4 < N#0 ==> Seq#Index(a#0, k#4) != x#0);
    havoc k#5;
    assume true;
    assume LitInt(0) <= k#5;
    assume k#5 < N#0;
    assert 0 <= k#5 && k#5 < Seq#Length(a#0);
    assume Seq#Index(a#0, k#5) == y#0;
}



procedure Call$$_module.__default.QuantifierRange1(_module._default.QuantifierRange1$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange1$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange1$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange1$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange1$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange1$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange1$T, $Heap), 
    N#0: int);
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  requires N#0 <= Seq#Length(a#0);
  requires (forall k#1: int :: 
    { Seq#Index(a#0, k#1) } 
    true ==> LitInt(0) <= k#1 && k#1 < N#0 ==> Seq#Index(a#0, k#1) != x#0);
  requires (exists k#6: int :: 
    { Seq#Index(a#0, k#6) } 
    LitInt(0) <= k#6 && k#6 < N#0 && Seq#Index(a#0, k#6) == y#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall k#4: int :: 
    { Seq#Index(a#0, k#4) } 
    LitInt(0) <= k#4 && k#4 < N#0 ==> Seq#Index(a#0, k#4) != x#0);
  free ensures true;
  ensures (exists k#7: int :: 
    { Seq#Index(a#0, k#7) } 
    LitInt(0) <= k#7 && k#7 < N#0 && Seq#Index(a#0, k#7) == y#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.QuantifierRange1(_module._default.QuantifierRange1$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange1$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange1$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange1$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange1$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange1$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange1$T, $Heap), 
    N#0: int)
   returns ($_reverifyPost: bool);
  free requires 69 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  requires N#0 <= Seq#Length(a#0);
  requires (forall k#1: int :: 
    { Seq#Index(a#0, k#1) } 
    true ==> LitInt(0) <= k#1 && k#1 < N#0 ==> Seq#Index(a#0, k#1) != x#0);
  requires (exists k#6: int :: 
    { Seq#Index(a#0, k#6) } 
    LitInt(0) <= k#6 && k#6 < N#0 && Seq#Index(a#0, k#6) == y#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall k#4: int :: 
    { Seq#Index(a#0, k#4) } 
    LitInt(0) <= k#4 && k#4 < N#0 ==> Seq#Index(a#0, k#4) != x#0);
  free ensures true;
  ensures (exists k#7: int :: 
    { Seq#Index(a#0, k#7) } 
    LitInt(0) <= k#7 && k#7 < N#0 && Seq#Index(a#0, k#7) == y#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.QuantifierRange1(_module._default.QuantifierRange1$T: Ty, 
    a#0: Seq Box, 
    x#0: Box, 
    y#0: Box, 
    N#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: QuantifierRange1, Impl$$_module.__default.QuantifierRange1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(325,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(326,3)
    assume true;
    assert x#0 != y#0;
}



procedure CheckWellformed$$_module.__default.QuantifierRange2(_module._default.QuantifierRange2$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange2$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange2$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange2$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange2$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange2$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange2$T, $Heap), 
    N#0: int);
  free requires 70 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.QuantifierRange2(_module._default.QuantifierRange2$T: Ty, 
    a#0: Seq Box, 
    x#0: Box, 
    y#0: Box, 
    N#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var k#1: int;

    // AddMethodImpl: QuantifierRange2, CheckWellformed$$_module.__default.QuantifierRange2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(329,7): initial state"} true;
    if (LitInt(0) <= N#0)
    {
    }

    assume LitInt(0) <= N#0 && N#0 <= Seq#Length(a#0);
    havoc k#0;
    assume true;
    assume LitInt(0) <= k#0;
    assume k#0 < N#0;
    assert 0 <= k#0 && k#0 < Seq#Length(a#0);
    assume Seq#Index(a#0, k#0) == y#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(332,10): post-state"} true;
    havoc k#1;
    assume true;
    if (*)
    {
        assume LitInt(0) <= k#1;
        assume k#1 < N#0;
        assert 0 <= k#1 && k#1 < Seq#Length(a#0);
        assume Seq#Index(a#0, k#1) == y#0;
    }
    else
    {
        assume LitInt(0) <= k#1 && k#1 < N#0 ==> Seq#Index(a#0, k#1) == y#0;
    }

    assume (forall k#2: int :: 
      { Seq#Index(a#0, k#2) } 
      LitInt(0) <= k#2 && k#2 < N#0 ==> Seq#Index(a#0, k#2) == y#0);
}



procedure Call$$_module.__default.QuantifierRange2(_module._default.QuantifierRange2$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange2$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange2$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange2$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange2$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange2$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange2$T, $Heap), 
    N#0: int);
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  requires N#0 <= Seq#Length(a#0);
  requires (exists k#3: int :: 
    { Seq#Index(a#0, k#3) } 
    LitInt(0) <= k#3 && k#3 < N#0 && Seq#Index(a#0, k#3) == y#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall k#2: int :: 
    { Seq#Index(a#0, k#2) } 
    LitInt(0) <= k#2 && k#2 < N#0 ==> Seq#Index(a#0, k#2) == y#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.QuantifierRange2(_module._default.QuantifierRange2$T: Ty, 
    a#0: Seq Box
       where $Is(a#0, TSeq(_module._default.QuantifierRange2$T))
         && $IsAlloc(a#0, TSeq(_module._default.QuantifierRange2$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.QuantifierRange2$T)
         && $IsAllocBox(x#0, _module._default.QuantifierRange2$T, $Heap), 
    y#0: Box
       where $IsBox(y#0, _module._default.QuantifierRange2$T)
         && $IsAllocBox(y#0, _module._default.QuantifierRange2$T, $Heap), 
    N#0: int)
   returns ($_reverifyPost: bool);
  free requires 70 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= N#0;
  requires N#0 <= Seq#Length(a#0);
  requires (exists k#3: int :: 
    { Seq#Index(a#0, k#3) } 
    LitInt(0) <= k#3 && k#3 < N#0 && Seq#Index(a#0, k#3) == y#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall k#2: int :: 
    { Seq#Index(a#0, k#2) } 
    LitInt(0) <= k#2 && k#2 < N#0 ==> Seq#Index(a#0, k#2) == y#0);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.QuantifierRange2(_module._default.QuantifierRange2$T: Ty, 
    a#0: Seq Box, 
    x#0: Box, 
    y#0: Box, 
    N#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0_0: int;
  var k#4: int;

    // AddMethodImpl: QuantifierRange2, Impl$$_module.__default.QuantifierRange2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(333,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(334,3)
    assume true;
    assert N#0 != 0;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(335,3)
    assume true;
    if (N#0 == LitInt(1))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(336,5)
        // Begin Comprehension WF check
        havoc k#0_0;
        if (true)
        {
            if (LitInt(0) <= k#0_0)
            {
            }

            if (LitInt(0) <= k#0_0 && k#0_0 < N#0)
            {
            }
            else
            {
            }

            assert {:subsumption 0} 0 <= (if LitInt(0) <= k#0_0 && k#0_0 < N#0 then k#0_0 else 0)
               && (if LitInt(0) <= k#0_0 && k#0_0 < N#0 then k#0_0 else 0) < Seq#Length(a#0);
            if (Seq#Index(a#0, (if LitInt(0) <= k#0_0 && k#0_0 < N#0 then k#0_0 else 0)) != y#0)
            {
                if (0 <= k#0_0)
                {
                }
            }
        }

        // End Comprehension WF check
        assume true;
        assert (forall k#0_1: int :: 
          {:nowarn} 
          Seq#Index(a#0, (if LitInt(0) <= k#0_1 && k#0_1 < N#0 then k#0_1 else 0)) != y#0
             ==> k#0_1 < 0 || N#0 <= k#0_1);
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(338,3)
    // Begin Comprehension WF check
    havoc k#4;
    if (true)
    {
        if (LitInt(0) <= k#4)
        {
        }

        if (LitInt(0) <= k#4 && k#4 < N#0)
        {
            assert 0 <= k#4 && k#4 < Seq#Length(a#0);
        }
    }

    // End Comprehension WF check
    assume true;
    if ((forall k#5: int :: 
      { Seq#Index(a#0, k#5) } 
      LitInt(0) <= k#5 && k#5 < N#0 ==> Seq#Index(a#0, k#5) == x#0))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(339,5)
        assume true;
        assert x#0 == y#0;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.M(zeros#0: Seq Box
       where $Is(zeros#0, TSeq(TBool)) && $IsAlloc(zeros#0, TSeq(TBool), $Heap), 
    Z#0: bool);
  free requires 71 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.M(zeros#0: Seq Box, Z#0: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;

    // AddMethodImpl: M, CheckWellformed$$_module.__default.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(345,13): initial state"} true;
    assume LitInt(1) <= Seq#Length(zeros#0);
    assume Z#0 == Lit(false);
    havoc k#0;
    assume true;
    if (*)
    {
        assume LitInt(0) <= k#0;
        assume k#0 < Seq#Length(zeros#0);
        assert 0 <= k#0 && k#0 < Seq#Length(zeros#0);
        assume $Unbox(Seq#Index(zeros#0, k#0)): bool == Z#0;
    }
    else
    {
        assume LitInt(0) <= k#0 && k#0 < Seq#Length(zeros#0)
           ==> $Unbox(Seq#Index(zeros#0, k#0)): bool == Z#0;
    }

    assume (forall k#1: int :: 
      { $Unbox(Seq#Index(zeros#0, k#1)): bool } 
      true
         ==> 
        LitInt(0) <= k#1 && k#1 < Seq#Length(zeros#0)
         ==> $Unbox(Seq#Index(zeros#0, k#1)): bool == Z#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
}



procedure Call$$_module.__default.M(zeros#0: Seq Box
       where $Is(zeros#0, TSeq(TBool)) && $IsAlloc(zeros#0, TSeq(TBool), $Heap), 
    Z#0: bool);
  // user-defined preconditions
  requires LitInt(1) <= Seq#Length(zeros#0);
  requires Z#0 == Lit(false);
  requires (forall k#1: int :: 
    { $Unbox(Seq#Index(zeros#0, k#1)): bool } 
    true
       ==> 
      LitInt(0) <= k#1 && k#1 < Seq#Length(zeros#0)
       ==> $Unbox(Seq#Index(zeros#0, k#1)): bool == Z#0);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.M(zeros#0: Seq Box
       where $Is(zeros#0, TSeq(TBool)) && $IsAlloc(zeros#0, TSeq(TBool), $Heap), 
    Z#0: bool)
   returns ($_reverifyPost: bool);
  free requires 71 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(1) <= Seq#Length(zeros#0);
  requires Z#0 == Lit(false);
  requires (forall k#1: int :: 
    { $Unbox(Seq#Index(zeros#0, k#1)): bool } 
    true
       ==> 
      LitInt(0) <= k#1 && k#1 < Seq#Length(zeros#0)
       ==> $Unbox(Seq#Index(zeros#0, k#1)): bool == Z#0);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.M(zeros#0: Seq Box, Z#0: bool) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: Seq Box where $Is(x#0, TSeq(TBool)) && $IsAlloc(x#0, TSeq(TBool), $Heap);

    // AddMethodImpl: M, Impl$$_module.__default.M
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(348,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(349,9)
    assume true;
    assume true;
    x#0 := Seq#Build(Seq#Empty(): Seq Box, $Box(Z#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(349,14)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(350,3)
    assert {:subsumption 0} 0 <= LitInt(0) && LitInt(0) <= Seq#Length(zeros#0);
    assert {:subsumption 0} LitInt(0) <= LitInt(1) && LitInt(1) <= Seq#Length(zeros#0);
    assume true;
    assert Seq#Equal(Seq#Drop(Seq#Take(zeros#0, LitInt(1)), LitInt(0)), 
      Seq#Build(Seq#Empty(): Seq Box, $Box(Z#0)));
}



procedure CheckWellformed$$_module.__default.TestSequences0();
  free requires 72 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestSequences0();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestSequences0() returns ($_reverifyPost: bool);
  free requires 72 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestSequences0() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap);
  var n#0: int;

    // AddMethodImpl: TestSequences0, Impl$$_module.__default.TestSequences0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(368,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(369,9)
    assume true;
    assume true;
    s#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(0))), $Box(LitInt(2))), 
        $Box(LitInt(4))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(369,20)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(370,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(371,5)
        assume true;
        assert Seq#Contains(s#0, $Box(4));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(372,5)
        assume true;
        assert Seq#Contains(s#0, $Box(0));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(373,5)
        assume true;
        assert !Seq#Contains(s#0, $Box(1));
    }
    else
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(375,5)
        assume true;
        assert Seq#Contains(s#0, $Box(2));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(376,5)
        assume true;
        assert Seq#Contains(s#0, $Box(0));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(377,5)
        // Begin Comprehension WF check
        havoc n#0;
        if (true)
        {
            if (Seq#Contains(s#0, $Box(n#0)))
            {
                if (LitInt(-3) <= n#0)
                {
                }
            }
        }

        // End Comprehension WF check
        assume true;
        assert (exists n#1: int :: 
          { Seq#Contains(s#0, $Box(n#1)) } 
          Seq#Contains(s#0, $Box(n#1)) && LitInt(-3) <= n#1 && n#1 < 2);
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(379,3)
    assume true;
    assert Seq#Contains(s#0, $Box(7));
}



procedure CheckWellformed$$_module.__default.test0();
  free requires 73 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test0();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.test0() returns ($_reverifyPost: bool);
  free requires 73 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.test0() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: test0, Impl$$_module.__default.test0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(385,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(386,3)
    assume true;
    assert false;
}



procedure {:verify false} CheckWellformed$$_module.__default.test1();
  free requires 74 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:verify false} Call$$_module.__default.test1();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure {:verify false} Impl$$_module.__default.test1() returns ($_reverifyPost: bool);
  free requires 74 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation {:verify false} Impl$$_module.__default.test1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: test1, Impl$$_module.__default.test1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(390,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(391,3)
    assume true;
    assert false;
}



// function declaration for _module._default.test2
function _module.__default.test2($ly: LayerType) : bool;

function _module.__default.test2#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.test2($LS($ly)) } 
  _module.__default.test2($LS($ly)) == _module.__default.test2($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.test2(AsFuelBottom($ly)) } 
  _module.__default.test2($ly) == _module.__default.test2($LZ));

// consequence axiom for _module.__default.test2
axiom 45 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.test2($ly) } 
    _module.__default.test2#canCall() || 45 != $FunctionContextHeight ==> true);

function _module.__default.test2#requires(LayerType) : bool;

// #requires axiom for _module.__default.test2
axiom (forall $ly: LayerType :: 
  { _module.__default.test2#requires($ly) } 
  _module.__default.test2#requires($ly) == true);

// definition axiom for _module.__default.test2 (revealed)
axiom 45 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.test2($LS($ly)) } 
    _module.__default.test2#canCall() || 45 != $FunctionContextHeight
       ==> _module.__default.test2#canCall()
         && _module.__default.test2($LS($ly)) == !Lit(_module.__default.test2($ly)));

// definition axiom for _module.__default.test2 for all literals (revealed)
axiom 45 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    {:weight 3} { _module.__default.test2($LS($ly)) } 
    _module.__default.test2#canCall() || 45 != $FunctionContextHeight
       ==> _module.__default.test2#canCall()
         && _module.__default.test2($LS($ly)) == !Lit(_module.__default.test2($LS($ly))));

procedure CheckWellformed$$_module.__default.test2();
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.test2()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function test2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(394,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert false;
        assume _module.__default.test2#canCall();
        assume _module.__default.test2($LS($LZ)) == !Lit(_module.__default.test2($LS($LZ)));
        assume _module.__default.test2#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.test2($LS($LZ)), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.test3
function _module.__default.test3($ly: LayerType) : bool;

function _module.__default.test3#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.test3($LS($ly)) } 
  _module.__default.test3($LS($ly)) == _module.__default.test3($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.test3(AsFuelBottom($ly)) } 
  _module.__default.test3($ly) == _module.__default.test3($LZ));

// consequence axiom for _module.__default.test3
axiom 46 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.test3($ly) } 
    _module.__default.test3#canCall() || 46 != $FunctionContextHeight ==> true);

function _module.__default.test3#requires(LayerType) : bool;

// #requires axiom for _module.__default.test3
axiom (forall $ly: LayerType :: 
  { _module.__default.test3#requires($ly) } 
  _module.__default.test3#requires($ly) == true);

// definition axiom for _module.__default.test3 (revealed)
axiom 46 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.test3($LS($ly)) } 
    _module.__default.test3#canCall() || 46 != $FunctionContextHeight
       ==> _module.__default.test3#canCall()
         && _module.__default.test3($LS($ly)) == !Lit(_module.__default.test3($ly)));

// definition axiom for _module.__default.test3 for all literals (revealed)
axiom 46 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    {:weight 3} { _module.__default.test3($LS($ly)) } 
    _module.__default.test3#canCall() || 46 != $FunctionContextHeight
       ==> _module.__default.test3#canCall()
         && _module.__default.test3($LS($ly)) == !Lit(_module.__default.test3($LS($ly))));

procedure {:verify false} CheckWellformed$$_module.__default.test3();
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:verify false} CheckWellformed$$_module.__default.test3()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function test3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(399,25): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert false;
        assume _module.__default.test3#canCall();
        assume _module.__default.test3($LS($LZ)) == !Lit(_module.__default.test3($LS($LZ)));
        assume _module.__default.test3#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.test3($LS($LZ)), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.F
function _module.__default.F(b#0: bool) : int;

function _module.__default.F#canCall(b#0: bool) : bool;

// consequence axiom for _module.__default.F
axiom 47 <= $FunctionContextHeight
   ==> (forall b#0: bool :: 
    { _module.__default.F(b#0) } 
    _module.__default.F#canCall(b#0) || 47 != $FunctionContextHeight
       ==> (if b#0
         then _module.__default.F(b#0) == LitInt(5)
         else _module.__default.F(b#0) == LitInt(6)));

function _module.__default.F#requires(bool) : bool;

// #requires axiom for _module.__default.F
axiom (forall b#0: bool :: 
  { _module.__default.F#requires(b#0) } 
  _module.__default.F#requires(b#0) == true);

// definition axiom for _module.__default.F (revealed)
axiom 47 <= $FunctionContextHeight
   ==> (forall b#0: bool :: 
    { _module.__default.F(b#0) } 
    _module.__default.F#canCall(b#0) || 47 != $FunctionContextHeight
       ==> _module.__default.F(b#0) == LitInt(5));

// definition axiom for _module.__default.F for all literals (revealed)
axiom 47 <= $FunctionContextHeight
   ==> (forall b#0: bool :: 
    {:weight 3} { _module.__default.F(Lit(b#0)) } 
    _module.__default.F#canCall(Lit(b#0)) || 47 != $FunctionContextHeight
       ==> _module.__default.F(Lit(b#0)) == LitInt(5));

procedure CheckWellformed$$_module.__default.F(b#0: bool);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures b#0 ==> _module.__default.F(b#0) == LitInt(5);
  ensures !b#0 ==> _module.__default.F(b#0) == LitInt(6);



implementation CheckWellformed$$_module.__default.F(b#0: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b#0: bool;
  var ##b#1: bool;


    // AddWellformednessCheck for function F
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(440,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (*)
        {
            assume b#0;
            ##b#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TBool, $Heap);
            assert b#0 == b#0 || (!##b#0 && b#0);
            assume b#0 == b#0 || _module.__default.F#canCall(b#0);
            assume _module.__default.F(b#0) == LitInt(5);
        }
        else
        {
            assume !b#0;
            ##b#1 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1, TBool, $Heap);
            assert b#0 == b#0 || (!##b#1 && b#0);
            assume b#0 == b#0 || _module.__default.F#canCall(b#0);
            assume _module.__default.F(b#0) == LitInt(6);
        }

        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.__default.F(b#0) == LitInt(5);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.F(b#0), TInt);
    }
}



procedure CheckWellformed$$_module.__default.TestAttributesVarDecls();
  free requires 75 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestAttributesVarDecls();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestAttributesVarDecls() returns ($_reverifyPost: bool);
  free requires 75 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure CheckWellformed$$_module.__default.TestNotNot();
  free requires 76 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TestNotNot();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TestNotNot() returns ($_reverifyPost: bool);
  free requires 76 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TestNotNot() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TestNotNot, Impl$$_module.__default.TestNotNot
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(568,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(569,3)
    assume true;
    assert !!Lit(true);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(571,3)
    assume true;
    assert !(Lit(true) == Lit(false));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(573,3)
    if (Lit(true))
    {
    }
    else
    {
    }

    assume true;
    assert {:subsumption 0} !(Lit(true) && Lit(false));
    assert {:subsumption 0} !(!Lit(true) && Lit(false));
    assume !(if true then false else false);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(575,3)
    if (Lit(true))
    {
    }
    else
    {
    }

    assume true;
    assert {:subsumption 0} !(Lit(true) && Lit(false));
    assert {:subsumption 0} !(!Lit(true) && Lit(false));
    assume !(if true then false else false);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(577,3)
    if (!!Lit(true))
    {
    }
    else
    {
    }

    assume true;
    assert {:subsumption 0} !(!!Lit(true) && Lit(false));
    assert {:subsumption 0} !(!Lit(true) && Lit(false));
    assume !(if !!Lit(true) then false else false);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(579,3)
    assume true;
    assert Lit(true) == !!Lit(true);
}



procedure CheckWellformed$$_module.__default.AssignSuchThat0(a#0: int, b#0: int) returns (x#0: int, y#0: int);
  free requires 77 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat0(a#0: int, b#0: int) returns (x#0: int, y#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == a#0;
  ensures y#0 == b#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat0(a#0: int, b#0: int) returns (x#0: int, y#0: int, $_reverifyPost: bool);
  free requires 77 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == a#0;
  ensures y#0 == b#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat0(a#0: int, b#0: int) returns (x#0: int, y#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0_0: int;
  var y#0_0: int;
  var xx#0: int;
  var yy#0: int;
  var xx#1: int;
  var yy#1: int;
  var $rhs#0: int;
  var $rhs#1: int;

    // AddMethodImpl: AssignSuchThat0, Impl$$_module.__default.AssignSuchThat0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(586,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(587,3)
    if (*)
    {
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(588,10)
        havoc x#0_0;
        havoc y#0_0;
        if (true)
        {
            if (a#0 <= x#0_0)
            {
            }

            if (a#0 <= x#0_0 && x#0_0 < a#0 + 1)
            {
            }

            if (a#0 <= x#0_0 && x#0_0 < a#0 + 1 && b#0 + a#0 <= y#0_0 + a#0)
            {
            }

            assume true;
        }

        assert (
            $Is(a#0 + 1 - 1, TInt)
             && $Is(b#0 + 1 - 1, TInt)
             && 
            a#0 <= a#0 + 1 - 1
             && a#0 + 1 - 1 < a#0 + 1
             && b#0 + a#0 <= b#0 + 1 - 1 + a#0
             && b#0 + 1 - 1 <= b#0)
           || 
          (
            $Is(a#0, TInt)
             && $Is(b#0 + 1 - 1, TInt)
             && 
            a#0 <= a#0
             && a#0 < a#0 + 1
             && b#0 + a#0 <= b#0 + 1 - 1 + a#0
             && b#0 + 1 - 1 <= b#0)
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(b#0 + 1 - 1, TInt)
             && 
            a#0 <= LitInt(0)
             && 0 < a#0 + 1
             && b#0 + a#0 <= b#0 + 1 - 1 + a#0
             && b#0 + 1 - 1 <= b#0)
           || 
          (exists $as#x0_0#0_0: int :: 
            $Is(b#0 + 1 - 1, TInt)
               && 
              a#0 <= $as#x0_0#0_0
               && $as#x0_0#0_0 < a#0 + 1
               && b#0 + a#0 <= b#0 + 1 - 1 + a#0
               && b#0 + 1 - 1 <= b#0)
           || 
          (
            $Is(a#0 + 1 - 1, TInt)
             && $Is(b#0 + a#0 - a#0, TInt)
             && 
            a#0 <= a#0 + 1 - 1
             && a#0 + 1 - 1 < a#0 + 1
             && b#0 + a#0 <= b#0 + a#0 - a#0 + a#0
             && b#0 + a#0 - a#0 <= b#0)
           || 
          (
            $Is(a#0, TInt)
             && $Is(b#0 + a#0 - a#0, TInt)
             && 
            a#0 <= a#0
             && a#0 < a#0 + 1
             && b#0 + a#0 <= b#0 + a#0 - a#0 + a#0
             && b#0 + a#0 - a#0 <= b#0)
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(b#0 + a#0 - a#0, TInt)
             && 
            a#0 <= LitInt(0)
             && 0 < a#0 + 1
             && b#0 + a#0 <= b#0 + a#0 - a#0 + a#0
             && b#0 + a#0 - a#0 <= b#0)
           || 
          (exists $as#x0_0#0_0: int :: 
            $Is(b#0 + a#0 - a#0, TInt)
               && 
              a#0 <= $as#x0_0#0_0
               && $as#x0_0#0_0 < a#0 + 1
               && b#0 + a#0 <= b#0 + a#0 - a#0 + a#0
               && b#0 + a#0 - a#0 <= b#0)
           || 
          (
            $Is(a#0 + 1 - 1, TInt)
             && $Is(LitInt(0), TInt)
             && 
            a#0 <= a#0 + 1 - 1
             && a#0 + 1 - 1 < a#0 + 1
             && b#0 + a#0 <= 0 + a#0
             && LitInt(0) <= b#0)
           || 
          (
            $Is(a#0, TInt)
             && $Is(LitInt(0), TInt)
             && 
            a#0 <= a#0
             && a#0 < a#0 + 1
             && b#0 + a#0 <= 0 + a#0
             && LitInt(0) <= b#0)
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(LitInt(0), TInt)
             && 
            a#0 <= LitInt(0)
             && 0 < a#0 + 1
             && b#0 + a#0 <= 0 + a#0
             && LitInt(0) <= b#0)
           || 
          (exists $as#x0_0#0_0: int :: 
            $Is(LitInt(0), TInt)
               && 
              a#0 <= $as#x0_0#0_0
               && $as#x0_0#0_0 < a#0 + 1
               && b#0 + a#0 <= 0 + a#0
               && LitInt(0) <= b#0)
           || 
          (exists $as#y0_0#0_0: int :: 
            $Is(a#0 + 1 - 1, TInt)
               && 
              a#0 <= a#0 + 1 - 1
               && a#0 + 1 - 1 < a#0 + 1
               && b#0 + a#0 <= $as#y0_0#0_0 + a#0
               && $as#y0_0#0_0 <= b#0)
           || 
          (exists $as#y0_0#0_0: int :: 
            $Is(a#0, TInt)
               && 
              a#0 <= a#0
               && a#0 < a#0 + 1
               && b#0 + a#0 <= $as#y0_0#0_0 + a#0
               && $as#y0_0#0_0 <= b#0)
           || 
          (exists $as#y0_0#0_0: int :: 
            $Is(LitInt(0), TInt)
               && 
              a#0 <= LitInt(0)
               && 0 < a#0 + 1
               && b#0 + a#0 <= $as#y0_0#0_0 + a#0
               && $as#y0_0#0_0 <= b#0)
           || (exists $as#x0_0#0_0: int, $as#y0_0#0_0: int :: 
            a#0 <= $as#x0_0#0_0
               && $as#x0_0#0_0 < a#0 + 1
               && b#0 + a#0 <= $as#y0_0#0_0 + a#0
               && $as#y0_0#0_0 <= b#0);
        havoc x#0, y#0;
        assume a#0 <= x#0 && x#0 < a#0 + 1 && b#0 + a#0 <= y#0 + a#0 && y#0 <= b#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(588,54)"} true;
    }
    else
    {
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(590,16)
        havoc xx#1;
        havoc yy#1;
        if (true)
        {
            if (a#0 <= xx#1)
            {
            }

            if (a#0 <= xx#1 && xx#1 < a#0 + 1)
            {
            }

            if (a#0 <= xx#1 && xx#1 < a#0 + 1 && b#0 + a#0 <= yy#1 + a#0)
            {
            }

            assume true;
        }

        assert (
            $Is(a#0 + 1 - 1, TInt)
             && $Is(b#0 + 1 - 1, TInt)
             && 
            a#0 <= a#0 + 1 - 1
             && a#0 + 1 - 1 < a#0 + 1
             && b#0 + a#0 <= b#0 + 1 - 1 + a#0
             && b#0 + 1 - 1 <= b#0)
           || 
          (
            $Is(a#0, TInt)
             && $Is(b#0 + 1 - 1, TInt)
             && 
            a#0 <= a#0
             && a#0 < a#0 + 1
             && b#0 + a#0 <= b#0 + 1 - 1 + a#0
             && b#0 + 1 - 1 <= b#0)
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(b#0 + 1 - 1, TInt)
             && 
            a#0 <= LitInt(0)
             && 0 < a#0 + 1
             && b#0 + a#0 <= b#0 + 1 - 1 + a#0
             && b#0 + 1 - 1 <= b#0)
           || 
          (exists $as#xx0#0: int :: 
            $Is(b#0 + 1 - 1, TInt)
               && 
              a#0 <= $as#xx0#0
               && $as#xx0#0 < a#0 + 1
               && b#0 + a#0 <= b#0 + 1 - 1 + a#0
               && b#0 + 1 - 1 <= b#0)
           || 
          (
            $Is(a#0 + 1 - 1, TInt)
             && $Is(b#0 + a#0 - a#0, TInt)
             && 
            a#0 <= a#0 + 1 - 1
             && a#0 + 1 - 1 < a#0 + 1
             && b#0 + a#0 <= b#0 + a#0 - a#0 + a#0
             && b#0 + a#0 - a#0 <= b#0)
           || 
          (
            $Is(a#0, TInt)
             && $Is(b#0 + a#0 - a#0, TInt)
             && 
            a#0 <= a#0
             && a#0 < a#0 + 1
             && b#0 + a#0 <= b#0 + a#0 - a#0 + a#0
             && b#0 + a#0 - a#0 <= b#0)
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(b#0 + a#0 - a#0, TInt)
             && 
            a#0 <= LitInt(0)
             && 0 < a#0 + 1
             && b#0 + a#0 <= b#0 + a#0 - a#0 + a#0
             && b#0 + a#0 - a#0 <= b#0)
           || 
          (exists $as#xx0#0: int :: 
            $Is(b#0 + a#0 - a#0, TInt)
               && 
              a#0 <= $as#xx0#0
               && $as#xx0#0 < a#0 + 1
               && b#0 + a#0 <= b#0 + a#0 - a#0 + a#0
               && b#0 + a#0 - a#0 <= b#0)
           || 
          (
            $Is(a#0 + 1 - 1, TInt)
             && $Is(LitInt(0), TInt)
             && 
            a#0 <= a#0 + 1 - 1
             && a#0 + 1 - 1 < a#0 + 1
             && b#0 + a#0 <= 0 + a#0
             && LitInt(0) <= b#0)
           || 
          (
            $Is(a#0, TInt)
             && $Is(LitInt(0), TInt)
             && 
            a#0 <= a#0
             && a#0 < a#0 + 1
             && b#0 + a#0 <= 0 + a#0
             && LitInt(0) <= b#0)
           || 
          (
            $Is(LitInt(0), TInt)
             && $Is(LitInt(0), TInt)
             && 
            a#0 <= LitInt(0)
             && 0 < a#0 + 1
             && b#0 + a#0 <= 0 + a#0
             && LitInt(0) <= b#0)
           || 
          (exists $as#xx0#0: int :: 
            $Is(LitInt(0), TInt)
               && 
              a#0 <= $as#xx0#0
               && $as#xx0#0 < a#0 + 1
               && b#0 + a#0 <= 0 + a#0
               && LitInt(0) <= b#0)
           || 
          (exists $as#yy0#0: int :: 
            $Is(a#0 + 1 - 1, TInt)
               && 
              a#0 <= a#0 + 1 - 1
               && a#0 + 1 - 1 < a#0 + 1
               && b#0 + a#0 <= $as#yy0#0 + a#0
               && $as#yy0#0 <= b#0)
           || 
          (exists $as#yy0#0: int :: 
            $Is(a#0, TInt)
               && 
              a#0 <= a#0
               && a#0 < a#0 + 1
               && b#0 + a#0 <= $as#yy0#0 + a#0
               && $as#yy0#0 <= b#0)
           || 
          (exists $as#yy0#0: int :: 
            $Is(LitInt(0), TInt)
               && 
              a#0 <= LitInt(0)
               && 0 < a#0 + 1
               && b#0 + a#0 <= $as#yy0#0 + a#0
               && $as#yy0#0 <= b#0)
           || (exists $as#xx0#0: int, $as#yy0#0: int :: 
            a#0 <= $as#xx0#0
               && $as#xx0#0 < a#0 + 1
               && b#0 + a#0 <= $as#yy0#0 + a#0
               && $as#yy0#0 <= b#0);
        havoc xx#0, yy#0;
        assume a#0 <= xx#0 && xx#0 < a#0 + 1 && b#0 + a#0 <= yy#0 + a#0 && yy#0 <= b#0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(590,63)"} true;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(591,10)
        assume true;
        assume true;
        assume true;
        $rhs#0 := xx#0;
        assume true;
        $rhs#1 := yy#0;
        x#0 := $rhs#0;
        y#0 := $rhs#1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(591,18)"} true;
    }
}



procedure CheckWellformed$$_module.__default.AssignSuchThat1(a#0: int, b#0: int) returns (x#0: int, y#0: int);
  free requires 78 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat1(a#0: int, b#0: int) returns (x#0: int, y#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat1(a#0: int, b#0: int) returns (x#0: int, y#0: int, $_reverifyPost: bool);
  free requires 78 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat1(a#0: int, b#0: int) returns (x#0: int, y#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: int;
  var k#1: int;
  var k#2: int;
  var S#0: Set Box where $Is(S#0, TSet(TInt)) && $IsAlloc(S#0, TSet(TInt), $Heap);
  var T#0: Set Box where $Is(T#0, TSet(TInt)) && $IsAlloc(T#0, TSet(TInt), $Heap);
  var T#1: Set Box;

    // AddMethodImpl: AssignSuchThat1, Impl$$_module.__default.AssignSuchThat1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(596,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(597,15)
    havoc k#1;
    if (true)
    {
        if (LitInt(0) <= k#1)
        {
        }

        assume true;
    }

    havoc k#0;
    assume LitInt(0) <= k#0 && k#0 < a#0 - b#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(597,38)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(598,3)
    assume true;
    assert b#0 < a#0;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(599,5)
    havoc k#2;
    if (true)
    {
        assume true;
    }

    assert ($Is(LitInt(0), TInt) && LitInt(0) == LitInt(Mul(LitInt(2), LitInt(0))))
       || (exists $as#k0#0: int :: $as#k0#0 == Mul(LitInt(2), $as#k0#0));
    havoc k#0;
    assume k#0 == Mul(LitInt(2), k#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(599,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(600,3)
    assume true;
    assert k#0 == LitInt(0);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(601,9)
    assume true;
    assume true;
    S#0 := Lit(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(2))), $Box(LitInt(4))), 
        $Box(LitInt(7))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(601,20)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(602,9)
    havoc T#1;
    if ($Is(T#1, TSet(TInt)) && $IsAlloc(T#1, TSet(TInt), $Heap))
    {
        assume true;
    }

    assert ($Is(S#0, TSet(TInt)) && Set#Subset(S#0, S#0))
       || 
      ($Is(Lit(Set#Empty(): Set Box), TSet(TInt))
         && Set#Subset(Set#Empty(): Set Box, S#0))
       || (exists $as#T0#0: Set Box :: 
        $Is($as#T0#0, TSet(TInt)) && Set#Subset($as#T0#0, S#0));
    havoc T#0;
    assume Set#Subset(T#0, S#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(602,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(603,3)
    assume true;
    assert !T#0[$Box(LitInt(3))];
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(604,3)
    assume true;
    assert Set#Equal(T#0, Set#Empty(): Set Box);
}



procedure CheckWellformed$$_module.__default.AssignSuchThat2(i#0: int, 
    j#0: int, 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat2(i#0: int, 
    j#0: int, 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat2(i#0: int, 
    j#0: int, 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass._module.Node()))
         && $IsAlloc(S#0, TSet(Tclass._module.Node()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat2(i#0: int, j#0: int, S#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
  var $nw: ref;
  var a#0: ref
     where $Is(a#0, Tclass._System.array(TInt))
       && $IsAlloc(a#0, Tclass._System.array(TInt), $Heap);
  var t#0: int;
  var t#0_0: int;
  var n#0_0: ref;
  var $obj0: ref;
  var $index0: Field Box;
  var $obj1: ref;
  var $index1: Field Box;
  var $obj2: ref;
  var $rhs#0_0: int;
  var $rhs#0_1: int;
  var $rhs#0_2: ref where $Is($rhs#0_2, Tclass._module.Node?());
  var $rhs#1_0: ref where $Is($rhs#1_0, Tclass._module.Node?());
  var $rhs#1_1: ref where $Is($rhs#1_1, Tclass._module.Node?());
  var t#2_0: int;
  var $rhs#2_0: int;
  var $rhs#2_1: int;

    // AddMethodImpl: AssignSuchThat2, Impl$$_module.__default.AssignSuchThat2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(609,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(610,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    n#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(610,19)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(611,9)
    assume true;
    assert 0 <= LitInt(25);
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._System.array?(TInt);
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(25);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    a#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(611,22)"} true;
    havoc t#0;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(613,3)
    if (LitInt(0) <= i#0)
    {
    }

    if (LitInt(0) <= i#0 && i#0 < j#0)
    {
    }

    assume true;
    if (LitInt(0) <= i#0 && i#0 < j#0 && j#0 < 25)
    {
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(614,30)
        havoc t#0_0;
        havoc n#0_0;
        assert a#0 != a#0 || j#0 != i#0;
        assert a#0 != null;
        assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
        assume true;
        $obj0 := a#0;
        $index0 := IndexField(i#0);
        assert $_Frame[$obj0, $index0];
        assert a#0 != null;
        assert 0 <= j#0 && j#0 < _System.array.Length(a#0);
        assume true;
        $obj1 := a#0;
        $index1 := IndexField(j#0);
        assert $_Frame[$obj1, $index1];
        assert n#0 != null;
        assume true;
        $obj2 := n#0;
        assert $_Frame[$obj2, _module.Node.next];
        havoc $rhs#0_0;
        havoc $rhs#0_1;
        havoc $rhs#0_2 /* where $Is($rhs#0_2, Tclass._module.Node?()) */;
        $Heap := update($Heap, $obj0, $index0, $Box($rhs#0_0));
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, $index1, $Box($rhs#0_1));
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj2, _module.Node.next, $rhs#0_2);
        assume $IsGoodHeap($Heap);
        if ($Is(n#0_0, Tclass._module.Node())
           && $IsAlloc(n#0_0, Tclass._module.Node(), $Heap))
        {
            assume true;
        }

        havoc t#0, n#0;
        assume true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(614,43)"} true;
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(616,3)
    assert n#0 != null;
    assume true;
    if (read($Heap, n#0, _module.Node.next) != null)
    {
        // ----- assume statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(617,5)
        if (S#0[$Box(n#0)])
        {
            assert {:subsumption 0} n#0 != null;
        }

        assume true;
        assume S#0[$Box(n#0)] && S#0[$Box(read($Heap, n#0, _module.Node.next))];
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(618,25)
        assert n#0 != read($Heap, n#0, _module.Node.next);
        assert n#0 != null;
        assert read($Heap, n#0, _module.Node.next) != null;
        assume true;
        $obj0 := read($Heap, n#0, _module.Node.next);
        assert $_Frame[$obj0, _module.Node.next];
        assert n#0 != null;
        assume true;
        $obj1 := n#0;
        assert $_Frame[$obj1, _module.Node.next];
        havoc $rhs#1_0 /* where $Is($rhs#1_0, Tclass._module.Node?()) */;
        havoc $rhs#1_1 /* where $Is($rhs#1_1, Tclass._module.Node?()) */;
        $Heap := update($Heap, $obj0, _module.Node.next, $rhs#1_0);
        assume $IsGoodHeap($Heap);
        $Heap := update($Heap, $obj1, _module.Node.next, $rhs#1_1);
        assume $IsGoodHeap($Heap);
        if (true)
        {
            assert {:subsumption 0} n#0 != null;
            if (read($Heap, n#0, _module.Node.next) != null)
            {
                assert {:subsumption 0} n#0 != null;
                assert {:subsumption 0} read($Heap, n#0, _module.Node.next) != null;
                assert {:subsumption 0} n#0 != null;
            }

            assume true;
        }

        havoc ;
        assume read($Heap, n#0, _module.Node.next) != null
           && read($Heap, read($Heap, n#0, _module.Node.next), _module.Node.next)
             == read($Heap, n#0, _module.Node.next);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(618,73)"} true;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(619,10)
        if (LitInt(0) <= i#0)
        {
        }

        if (LitInt(0) <= i#0 && i#0 < 25)
        {
            if (LitInt(0) <= j#0)
            {
            }
        }

        assume true;
        if (LitInt(0) <= i#0 && i#0 < 25 && LitInt(0) <= j#0 && j#0 < 25)
        {
            // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(620,19)
            havoc t#2_0;
            assert a#0 != a#0 || j#0 != i#0;
            assert a#0 != null;
            assert 0 <= i#0 && i#0 < _System.array.Length(a#0);
            assume true;
            $obj0 := a#0;
            $index0 := IndexField(i#0);
            assert $_Frame[$obj0, $index0];
            assert a#0 != null;
            assert 0 <= j#0 && j#0 < _System.array.Length(a#0);
            assume true;
            $obj1 := a#0;
            $index1 := IndexField(j#0);
            assert $_Frame[$obj1, $index1];
            havoc $rhs#2_0;
            havoc $rhs#2_1;
            $Heap := update($Heap, $obj0, $index0, $Box($rhs#2_0));
            assume $IsGoodHeap($Heap);
            $Heap := update($Heap, $obj1, $index1, $Box($rhs#2_1));
            assume $IsGoodHeap($Heap);
            if (true)
            {
                assert a#0 != null;
                assert {:subsumption 0} 0 <= i#0 && i#0 < _System.array.Length(a#0);
                if (t#2_0 < $Unbox(read($Heap, a#0, IndexField(i#0))): int)
                {
                    assert a#0 != null;
                    assert {:subsumption 0} 0 <= i#0 && i#0 < _System.array.Length(a#0);
                    assert a#0 != null;
                    assert {:subsumption 0} 0 <= j#0 && j#0 < _System.array.Length(a#0);
                }

                assume true;
            }

            havoc t#0;
            assume t#0 < $Unbox(read($Heap, a#0, IndexField(i#0))): int
               && $Unbox(read($Heap, a#0, IndexField(i#0))): int
                 < $Unbox(read($Heap, a#0, IndexField(j#0))): int;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(620,43)"} true;
        }
        else
        {
        }
    }
}



procedure CheckWellformed$$_module.__default.AssignSuchThat3();
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat3();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat3() returns ($_reverifyPost: bool);
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat3() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap);
  var $nw: ref;
  var n#1: ref;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.Node?());

    // AddMethodImpl: AssignSuchThat3, Impl$$_module.__default.AssignSuchThat3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(625,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(626,16)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    n#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(626,26)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(627,13)
    havoc n#1;
    assert n#0 != null;
    assume true;
    assert $_Frame[n#0, _module.Node.next];
    havoc $rhs#0 /* where $Is($rhs#0, Tclass._module.Node?()) */;
    $Heap := update($Heap, n#0, _module.Node.next, $rhs#0);
    assume $IsGoodHeap($Heap);
    if ($Is(n#1, Tclass._module.Node?()) && $IsAlloc(n#1, Tclass._module.Node?(), $Heap))
    {
        assert {:subsumption 0} n#1 != null;
        assume true;
    }

    havoc n#0;
    assume read($Heap, n#0, _module.Node.next) == n#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(627,33)"} true;
}



procedure CheckWellformed$$_module.__default.AssignSuchThat4();
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat4();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat4() returns ($_reverifyPost: bool);
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat4() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: ref
     where $Is(n#0, Tclass._module.Node?()) && $IsAlloc(n#0, Tclass._module.Node?(), $Heap);
  var $nw: ref;
  var n#1: ref;
  var $rhs#0: ref where $Is($rhs#0, Tclass._module.Node?());

    // AddMethodImpl: AssignSuchThat4, Impl$$_module.__default.AssignSuchThat4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(631,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(632,16)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    n#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(632,26)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(633,13)
    havoc n#1;
    assert n#0 != null;
    assume true;
    assert $_Frame[n#0, _module.Node.next];
    havoc $rhs#0 /* where $Is($rhs#0, Tclass._module.Node?()) */;
    $Heap := update($Heap, n#0, _module.Node.next, $rhs#0);
    assume $IsGoodHeap($Heap);
    if ($Is(n#1, Tclass._module.Node?()) && $IsAlloc(n#1, Tclass._module.Node?(), $Heap))
    {
        if (n#1 != null)
        {
            assert {:subsumption 0} n#1 != null;
        }

        assume true;
    }

    havoc n#0;
    assume n#0 != null && read($Heap, n#0, _module.Node.next) == n#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(633,46)"} true;
}



procedure CheckWellformed$$_module.__default.AssignSuchThat5();
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat5();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat5() returns ($_reverifyPost: bool);
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat5() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#0: ref
     where $Is(k#0, Tclass._module.Node()) && $IsAlloc(k#0, Tclass._module.Node(), $Heap);
  var $nw: ref;
  var defass#n#0: bool;
  var n#0: ref
     where defass#n#0
       ==> $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
  var n#1: ref;

    // AddMethodImpl: AssignSuchThat5, Impl$$_module.__default.AssignSuchThat5
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(637,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(638,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.Node?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    k#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(638,19)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(639,21)
    havoc n#1;
    if ($Is(n#1, Tclass._module.Node()) && $IsAlloc(n#1, Tclass._module.Node(), $Heap))
    {
        assume true;
    }

    assert ($Is(null, Tclass._module.Node())
         && 
        null != null
         && !read(old($Heap), null, alloc))
       || (exists $as#n0#0: ref :: 
        $Is($as#n0#0, Tclass._module.Node())
           && 
          $as#n0#0 != null
           && !read(old($Heap), $as#n0#0, alloc));
    defass#n#0 := true;
    havoc n#0;
    assume n#0 != null && !read(old($Heap), n#0, alloc);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(639,31)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(640,3)
    assume true;
    assert false;
}



procedure CheckWellformed$$_module.__default.AssignSuchThat6();
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat6();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat6() returns ($_reverifyPost: bool);
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat6() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var defass#n#0: bool;
  var n#0: ref
     where defass#n#0
       ==> $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap);
  var n#1: ref;

    // AddMethodImpl: AssignSuchThat6, Impl$$_module.__default.AssignSuchThat6
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(644,0): initial state"} true;
    $_reverifyPost := false;
    havoc n#0 /* where defass#n#0
       ==> $Is(n#0, Tclass._module.Node()) && $IsAlloc(n#0, Tclass._module.Node(), $Heap) */;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(646,5)
    havoc n#1;
    if ($Is(n#1, Tclass._module.Node()) && $IsAlloc(n#1, Tclass._module.Node(), $Heap))
    {
        assume true;
    }

    defass#n#0 := true;
    havoc n#0;
    assume n#0 != null && !read(old($Heap), n#0, alloc);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(646,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(647,3)
    assume true;
    assert false;
}



procedure CheckWellformed$$_module.__default.AssignSuchThat7(_module._default.AssignSuchThat7$T: Ty, 
    A#0: Set Box
       where $Is(A#0, TSet(_module._default.AssignSuchThat7$T))
         && $IsAlloc(A#0, TSet(_module._default.AssignSuchThat7$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.AssignSuchThat7$T)
         && $IsAllocBox(x#0, _module._default.AssignSuchThat7$T, $Heap));
  free requires 79 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat7(_module._default.AssignSuchThat7$T: Ty, 
    A#0: Set Box
       where $Is(A#0, TSet(_module._default.AssignSuchThat7$T))
         && $IsAlloc(A#0, TSet(_module._default.AssignSuchThat7$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.AssignSuchThat7$T)
         && $IsAllocBox(x#0, _module._default.AssignSuchThat7$T, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat7(_module._default.AssignSuchThat7$T: Ty, 
    A#0: Set Box
       where $Is(A#0, TSet(_module._default.AssignSuchThat7$T))
         && $IsAlloc(A#0, TSet(_module._default.AssignSuchThat7$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module._default.AssignSuchThat7$T)
         && $IsAllocBox(x#0, _module._default.AssignSuchThat7$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 79 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat7(_module._default.AssignSuchThat7$T: Ty, A#0: Set Box, x#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var B#0: Set Box
     where $Is(B#0, TSet(_module._default.AssignSuchThat7$T))
       && $IsAlloc(B#0, TSet(_module._default.AssignSuchThat7$T), $Heap);
  var B#1: Set Box;

    // AddMethodImpl: AssignSuchThat7, Impl$$_module.__default.AssignSuchThat7
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(650,43): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(651,9)
    havoc B#1;
    if ($Is(B#1, TSet(_module._default.AssignSuchThat7$T))
       && $IsAlloc(B#1, TSet(_module._default.AssignSuchThat7$T), $Heap))
    {
        assume true;
    }

    assert ($Is(A#0, TSet(_module._default.AssignSuchThat7$T)) && Set#Subset(A#0, A#0))
       || 
      ($Is(Lit(Set#Empty(): Set Box), TSet(_module._default.AssignSuchThat7$T))
         && Set#Subset(Set#Empty(): Set Box, A#0))
       || (exists $as#B0#0: Set Box :: 
        $Is($as#B0#0, TSet(_module._default.AssignSuchThat7$T))
           && Set#Subset($as#B0#0, A#0));
    havoc B#0;
    assume Set#Subset(B#0, A#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(651,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(652,3)
    if (B#0[x#0])
    {
    }

    assume true;
    assert {:subsumption 0} B#0[x#0] ==> A#0[x#0];
    assume B#0[x#0] ==> A#0[x#0];
}



procedure CheckWellformed$$_module.__default.AssignSuchThat8(n#0: int)
   returns (x#0: int, 
    y#0: DatatypeType
       where $Is(y#0, Tclass._module.Lindgren())
         && $IsAlloc(y#0, Tclass._module.Lindgren(), $Heap));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat8(n#0: int)
   returns (x#0: int, 
    y#0: DatatypeType
       where $Is(y#0, Tclass._module.Lindgren())
         && $IsAlloc(y#0, Tclass._module.Lindgren(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat8(n#0: int)
   returns (x#0: int, 
    defass#y#0: bool, 
    y#0: DatatypeType
       where defass#y#0
         ==> $Is(y#0, Tclass._module.Lindgren())
           && $IsAlloc(y#0, Tclass._module.Lindgren(), $Heap), 
    $_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat8(n#0: int)
   returns (x#0: int, defass#y#0: bool, y#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#1: int;
  var x#2: int;
  var x#3: int;
  var y#1: DatatypeType;
  var y#2: DatatypeType;
  var x#4: int;
  var x#5: int;
  var x#6: int;
  var x#7: int;

    // AddMethodImpl: AssignSuchThat8, Impl$$_module.__default.AssignSuchThat8
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(655,61): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(656,5)
    havoc x#1;
    if (true)
    {
        assume true;
    }

    assert ($Is(LitInt(1), TInt) && LitInt(1) == LitInt(1))
       || 
      ($Is(LitInt(0), TInt) && LitInt(0) == LitInt(1))
       || (exists $as#x0#0: int :: $as#x0#0 == LitInt(1));
    havoc x#0;
    assume x#0 == LitInt(1);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(656,15)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(657,5)
    havoc x#2;
    if (true)
    {
        assume true;
    }

    assert ($Is(LitInt(11), TInt)
         && (LitInt(11) == LitInt(3) || LitInt(11) == LitInt(7) || LitInt(11) == LitInt(11)))
       || 
      ($Is(LitInt(7), TInt)
         && (LitInt(7) == LitInt(3) || LitInt(7) == LitInt(7) || LitInt(7) == LitInt(11)))
       || 
      ($Is(LitInt(3), TInt)
         && (LitInt(3) == LitInt(3) || LitInt(3) == LitInt(7) || LitInt(3) == LitInt(11)))
       || 
      ($Is(LitInt(0), TInt)
         && (LitInt(0) == LitInt(3) || LitInt(0) == LitInt(7) || LitInt(0) == LitInt(11)))
       || (exists $as#x1#0: int :: 
        $as#x1#0 == LitInt(3) || $as#x1#0 == LitInt(7) || $as#x1#0 == LitInt(11));
    havoc x#0;
    assume x#0 == LitInt(3) || x#0 == LitInt(7) || x#0 == LitInt(11);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(657,22)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(658,5)
    havoc x#3;
    if (true)
    {
        assume true;
    }

    assert ($Is(n#0 + 12, TInt) && n#0 + 12 == n#0 + 12)
       || 
      ($Is(LitInt(0), TInt) && LitInt(0) == n#0 + 12)
       || (exists $as#x2#0: int :: $as#x2#0 == n#0 + 12);
    havoc x#0;
    assume x#0 == n#0 + 12;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(658,20)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(659,5)
    havoc y#1;
    if ($Is(y#1, Tclass._module.Lindgren())
       && $IsAlloc(y#1, Tclass._module.Lindgren(), $Heap))
    {
        assume true;
    }

    assert ($Is(Lit(#_module.Lindgren.HerrNilsson()), Tclass._module.Lindgren())
         && Lit(#_module.Lindgren.HerrNilsson()) == Lit(#_module.Lindgren.HerrNilsson()))
       || 
      ($Is(Lit(#_module.Lindgren.HerrNilsson()), Tclass._module.Lindgren())
         && Lit(#_module.Lindgren.HerrNilsson()) == Lit(#_module.Lindgren.HerrNilsson()))
       || (exists $as#y0#0: DatatypeType :: 
        $Is($as#y0#0, Tclass._module.Lindgren())
           && $as#y0#0 == Lit(#_module.Lindgren.HerrNilsson()));
    defass#y#0 := true;
    havoc y#0;
    assume y#0 == Lit(#_module.Lindgren.HerrNilsson());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(659,25)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(660,5)
    havoc y#2;
    if ($Is(y#2, Tclass._module.Lindgren())
       && $IsAlloc(y#2, Tclass._module.Lindgren(), $Heap))
    {
        assume $IsA#_module.Lindgren(y#2) && $IsA#_module.Lindgren(y#2);
    }

    assert ($Is(Lit(#_module.Lindgren.HerrNilsson()), Tclass._module.Lindgren())
         && _module.Lindgren#Equal(#_module.Lindgren.HerrNilsson(), #_module.Lindgren.HerrNilsson()))
       || (exists $as#y1#0: DatatypeType :: 
        $Is($as#y1#0, Tclass._module.Lindgren())
           && _module.Lindgren#Equal($as#y1#0, $as#y1#0));
    defass#y#0 := true;
    havoc y#0;
    assume _module.Lindgren#Equal(y#0, y#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(660,13)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(661,5)
    havoc x#4;
    if (true)
    {
        assume true;
    }

    assert ($Is(LitInt(3), TInt)
         && (
          LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(2)
           || LitInt(3) == LitInt(3)))
       || 
      ($Is(LitInt(2), TInt)
         && (
          LitInt(2) == LitInt(3)
           || LitInt(2) == LitInt(3)
           || LitInt(2) == LitInt(2)
           || LitInt(2) == LitInt(3)))
       || 
      ($Is(LitInt(3), TInt)
         && (
          LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(2)
           || LitInt(3) == LitInt(3)))
       || 
      ($Is(LitInt(3), TInt)
         && (
          LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(2)
           || LitInt(3) == LitInt(3)))
       || 
      ($Is(LitInt(0), TInt)
         && (
          LitInt(0) == LitInt(3)
           || LitInt(0) == LitInt(3)
           || LitInt(0) == LitInt(2)
           || LitInt(0) == LitInt(3)))
       || (exists $as#x3#0: int :: 
        $as#x3#0 == LitInt(3)
           || $as#x3#0 == LitInt(3)
           || $as#x3#0 == LitInt(2)
           || $as#x3#0 == LitInt(3));
    havoc x#0;
    assume x#0 == LitInt(3) || x#0 == LitInt(3) || x#0 == LitInt(2) || x#0 == LitInt(3);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(661,32)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(662,5)
    havoc x#5;
    if (true)
    {
        assume true;
    }

    assert ($Is(LitInt(0), TInt)
         && Map#Domain(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(5)), $Box(LitInt(10))), 
            $Box(LitInt(6)), 
            $Box(LitInt(12))))[$Box(0)])
       || (exists $as#x4#0: int :: 
        Map#Domain(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(5)), $Box(LitInt(10))), 
            $Box(LitInt(6)), 
            $Box(LitInt(12))))[$Box($as#x4#0)]);
    havoc x#0;
    assume Map#Domain(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(5)), $Box(LitInt(10))), 
        $Box(LitInt(6)), 
        $Box(LitInt(12))))[$Box(x#0)];
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(662,33)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(663,5)
    havoc x#6;
    if (true)
    {
        assume true;
    }

    assert ($Is(LitInt(2), TInt)
         && Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(2)))
       || 
      ($Is(n#0, TInt)
         && Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(n#0)))
       || 
      ($Is(n#0, TInt)
         && Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(n#0)))
       || 
      ($Is(LitInt(0), TInt)
         && Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(0)))
       || (exists $as#x5#0: int :: 
        Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box($as#x5#0)));
    havoc x#0;
    assume Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
        $Box(LitInt(2))), 
      $Box(x#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(663,21)"} true;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(664,5)
    havoc x#7;
    if (true)
    {
        assume true;
    }

    assert ($Is(LitInt(0), TInt) && Seq#Contains(Seq#Empty(): Seq Box, $Box(0)))
       || (exists $as#x6#0: int :: Seq#Contains(Seq#Empty(): Seq Box, $Box($as#x6#0)));
    havoc x#0;
    assume Seq#Contains(Seq#Empty(): Seq Box, $Box(x#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(664,14)"} true;
    assert defass#y#0;
}



procedure CheckWellformed$$_module.__default.AssignSuchThat9()
   returns (q#0: DatatypeType
       where $Is(q#0, Tclass._module.QuiteFinite())
         && $IsAlloc(q#0, Tclass._module.QuiteFinite(), $Heap));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AssignSuchThat9()
   returns (q#0: DatatypeType
       where $Is(q#0, Tclass._module.QuiteFinite())
         && $IsAlloc(q#0, Tclass._module.QuiteFinite(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.AssignSuchThat9()
   returns (q#0: DatatypeType
       where $Is(q#0, Tclass._module.QuiteFinite())
         && $IsAlloc(q#0, Tclass._module.QuiteFinite(), $Heap), 
    $_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.AssignSuchThat9() returns (q#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var q#1: DatatypeType;

    // AddMethodImpl: AssignSuchThat9, Impl$$_module.__default.AssignSuchThat9
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(670,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(671,5)
    havoc q#1;
    if ($Is(q#1, Tclass._module.QuiteFinite())
       && $IsAlloc(q#1, Tclass._module.QuiteFinite(), $Heap))
    {
        if (!$Eq#_module.QuiteFinite($LS($LS($LZ)), q#1, #_module.QuiteFinite.QQA()))
        {
        }

        assume $IsA#_module.QuiteFinite(q#1)
           && (!$Eq#_module.QuiteFinite($LS($LS($LZ)), q#1, #_module.QuiteFinite.QQA())
             ==> $IsA#_module.QuiteFinite(q#1));
    }

    assert ($Is(Lit(#_module.QuiteFinite.QQC()), Tclass._module.QuiteFinite())
         && 
        !$Eq#_module.QuiteFinite($LS($LS($LZ)), #_module.QuiteFinite.QQC(), #_module.QuiteFinite.QQA())
         && !$Eq#_module.QuiteFinite($LS($LS($LZ)), #_module.QuiteFinite.QQC(), #_module.QuiteFinite.QQC()))
       || 
      ($Is(Lit(#_module.QuiteFinite.QQB()), Tclass._module.QuiteFinite())
         && 
        !$Eq#_module.QuiteFinite($LS($LS($LZ)), #_module.QuiteFinite.QQB(), #_module.QuiteFinite.QQA())
         && !$Eq#_module.QuiteFinite($LS($LS($LZ)), #_module.QuiteFinite.QQB(), #_module.QuiteFinite.QQC()))
       || 
      ($Is(Lit(#_module.QuiteFinite.QQA()), Tclass._module.QuiteFinite())
         && 
        !$Eq#_module.QuiteFinite($LS($LS($LZ)), #_module.QuiteFinite.QQA(), #_module.QuiteFinite.QQA())
         && !$Eq#_module.QuiteFinite($LS($LS($LZ)), #_module.QuiteFinite.QQA(), #_module.QuiteFinite.QQC()))
       || (exists $as#q0#0: DatatypeType :: 
        $Is($as#q0#0, Tclass._module.QuiteFinite())
           && 
          !$Eq#_module.QuiteFinite($LS($LS($LZ)), $as#q0#0, #_module.QuiteFinite.QQA())
           && !$Eq#_module.QuiteFinite($LS($LS($LZ)), $as#q0#0, #_module.QuiteFinite.QQC()));
    havoc q#0;
    assume !$Eq#_module.QuiteFinite($LS($LS($LZ)), q#0, #_module.QuiteFinite.QQA())
       && !$Eq#_module.QuiteFinite($LS($LS($LZ)), q#0, #_module.QuiteFinite.QQC());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(671,27)"} true;
}



// function declaration for _module._default.LetSuchThat_P
function _module.__default.LetSuchThat__P(x#0: int) : bool;

function _module.__default.LetSuchThat__P#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.LetSuchThat__P
axiom 52 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.LetSuchThat__P(x#0) } 
    _module.__default.LetSuchThat__P#canCall(x#0) || 52 != $FunctionContextHeight
       ==> true);

function _module.__default.LetSuchThat__P#requires(int) : bool;

// #requires axiom for _module.__default.LetSuchThat__P
axiom (forall x#0: int :: 
  { _module.__default.LetSuchThat__P#requires(x#0) } 
  _module.__default.LetSuchThat__P#requires(x#0) == true);

procedure CheckWellformed$$_module.__default.LetSuchThat__P(x#0: int);
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.LetSuchThat0(g#0: int);
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LetSuchThat0(g#0: int);
  // user-defined preconditions
  requires _module.__default.LetSuchThat__P(g#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LetSuchThat0(g#0: int) returns ($_reverifyPost: bool);
  free requires 53 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.LetSuchThat__P(g#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function $let#0_q() : int;

function $let#0$canCall() : bool;

axiom $let#0$canCall() ==> _module.__default.LetSuchThat__P($let#0_q());

implementation Impl$$_module.__default.LetSuchThat0(g#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#0: int;
  var t#1: int;
  var ##x#1: int;
  var u#0: int;
  var q#0: int;
  var ##x#2: int;
  var a#0: int;
  var b#0: int;
  var ##x#3: int;
  var ##x#4: int;
  var ##x#5: int;
  var ##x#6: int;

    // AddMethodImpl: LetSuchThat0, Impl$$_module.__default.LetSuchThat0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(680,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(681,9)
    havoc t#1;
    if (true)
    {
        ##x#1 := t#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#1, TInt, $Heap);
        assume _module.__default.LetSuchThat__P#canCall(t#1);
        assume _module.__default.LetSuchThat__P#canCall(t#1);
    }

    assert ($Is(LitInt(0), TInt) && _module.__default.LetSuchThat__P(LitInt(0)))
       || (exists $as#t0#0: int :: _module.__default.LetSuchThat__P($as#t0#0));
    havoc t#0;
    assume _module.__default.LetSuchThat__P(t#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(681,27)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(682,15)
    assume true;
    havoc q#0;
    if (true)
    {
        ##x#2 := q#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#2, TInt, $Heap);
        assume _module.__default.LetSuchThat__P#canCall(q#0);
    }

    assert ($Is(LitInt(0), TInt) && _module.__default.LetSuchThat__P(LitInt(0)))
       || (exists q#1: int :: _module.__default.LetSuchThat__P(q#1));
    assume true;
    assume _module.__default.LetSuchThat__P(q#0);
    assume $let#0$canCall();
    assume $let#0$canCall();
    u#0 := (var q#1 := $let#0_q(); q#1 + 1);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(682,49)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(683,3)
    // Begin Comprehension WF check
    havoc a#0;
    havoc b#0;
    if (true)
    {
        ##x#3 := a#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#3, TInt, $Heap);
        assume _module.__default.LetSuchThat__P#canCall(a#0);
        if (_module.__default.LetSuchThat__P(a#0))
        {
            ##x#4 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#4, TInt, $Heap);
            assume _module.__default.LetSuchThat__P#canCall(b#0);
        }

        if (_module.__default.LetSuchThat__P(a#0) && _module.__default.LetSuchThat__P(b#0))
        {
        }
    }

    // End Comprehension WF check
    assume (forall a#1: int, b#1: int :: 
      { _module.__default.LetSuchThat__P(b#1), _module.__default.LetSuchThat__P(a#1) } 
      _module.__default.LetSuchThat__P#canCall(a#1)
         && (_module.__default.LetSuchThat__P(a#1)
           ==> _module.__default.LetSuchThat__P#canCall(b#1)));
    if ((forall a#1: int, b#1: int :: 
      { _module.__default.LetSuchThat__P(b#1), _module.__default.LetSuchThat__P(a#1) } 
      _module.__default.LetSuchThat__P(a#1) && _module.__default.LetSuchThat__P(b#1)
         ==> a#1 == b#1))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(684,5)
        assume true;
        assert t#0 < u#0;
    }
    else
    {
    }

    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(686,3)
    ##x#5 := u#0 - 1;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#5, TInt, $Heap);
    assume _module.__default.LetSuchThat__P#canCall(u#0 - 1);
    assume _module.__default.LetSuchThat__P#canCall(u#0 - 1);
    assert _module.__default.LetSuchThat__P(u#0 - 1);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(687,3)
    ##x#6 := u#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#6, TInt, $Heap);
    assume _module.__default.LetSuchThat__P#canCall(u#0);
    assume _module.__default.LetSuchThat__P#canCall(u#0);
    assert _module.__default.LetSuchThat__P(u#0);
}



procedure CheckWellformed$$_module.__default.LetSuchThat1(_module._default.LetSuchThat1$T: Ty, 
    A#0: Set Box
       where $Is(A#0, TSet(_module._default.LetSuchThat1$T))
         && $IsAlloc(A#0, TSet(_module._default.LetSuchThat1$T), $Heap));
  free requires 80 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LetSuchThat1(_module._default.LetSuchThat1$T: Ty, 
    A#0: Set Box
       where $Is(A#0, TSet(_module._default.LetSuchThat1$T))
         && $IsAlloc(A#0, TSet(_module._default.LetSuchThat1$T), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LetSuchThat1(_module._default.LetSuchThat1$T: Ty, 
    A#0: Set Box
       where $Is(A#0, TSet(_module._default.LetSuchThat1$T))
         && $IsAlloc(A#0, TSet(_module._default.LetSuchThat1$T), $Heap))
   returns ($_reverifyPost: bool);
  free requires 80 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function $let#1_B(_module._default.LetSuchThat1$T: Ty, A: Set Box) : Set Box;

function $let#1$canCall(_module._default.LetSuchThat1$T: Ty, A: Set Box) : bool;

axiom (forall _module._default.LetSuchThat1$T: Ty, A: Set Box :: 
  { $let#1_B(_module._default.LetSuchThat1$T, A) } 
  $let#1$canCall(_module._default.LetSuchThat1$T, A)
     ==> $Is($let#1_B(_module._default.LetSuchThat1$T, A), 
        TSet(_module._default.LetSuchThat1$T))
       && Set#Subset($let#1_B(_module._default.LetSuchThat1$T, A), A));

implementation Impl$$_module.__default.LetSuchThat1(_module._default.LetSuchThat1$T: Ty, A#0: Set Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var C#0: Set Box
     where $Is(C#0, TSet(_module._default.LetSuchThat1$T))
       && $IsAlloc(C#0, TSet(_module._default.LetSuchThat1$T), $Heap);
  var B#0: Set Box;

    // AddMethodImpl: LetSuchThat1, Impl$$_module.__default.LetSuchThat1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(691,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(692,15)
    assume true;
    havoc B#0;
    if ($Is(B#0, TSet(_module._default.LetSuchThat1$T)))
    {
    }

    assert ($Is(A#0, TSet(_module._default.LetSuchThat1$T)) && Set#Subset(A#0, A#0))
       || 
      ($Is(Lit(Set#Empty(): Set Box), TSet(_module._default.LetSuchThat1$T))
         && Set#Subset(Set#Empty(): Set Box, A#0))
       || (exists B#1: Set Box :: 
        $Is(B#1, TSet(_module._default.LetSuchThat1$T)) && Set#Subset(B#1, A#0));
    assume $Is(B#0, TSet(_module._default.LetSuchThat1$T));
    assume Set#Subset(B#0, A#0);
    assume $let#1$canCall(_module._default.LetSuchThat1$T, A#0);
    assume $let#1$canCall(_module._default.LetSuchThat1$T, A#0);
    C#0 := (var B#1 := $let#1_B(_module._default.LetSuchThat1$T, A#0); 
      Set#Difference(B#1, A#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(692,39)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(693,3)
    assume true;
    assert Set#Equal(C#0, Set#Empty(): Set Box);
}



procedure CheckWellformed$$_module.__default.LetSuchThat2(n#0: int where LitInt(0) <= n#0);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LetSuchThat2(n#0: int where LitInt(0) <= n#0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LetSuchThat2(n#0: int where LitInt(0) <= n#0) returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function $let#2_k(n: int) : int;

function $let#2$canCall(n: int) : bool;

axiom (forall n: int :: { $let#2_k(n) } $let#2$canCall(n) ==> $let#2_k(n) < n);

function $let#3_k(n: int) : int;

function $let#3$canCall(n: int) : bool;

axiom (forall n: int :: 
  { $let#3_k(n) } 
  $let#3$canCall(n) ==> LitInt(0) <= $let#3_k(n) && $let#3_k(n) < n);

function $let#4_k(n: int) : int;

function $let#4$canCall(n: int) : bool;

axiom (forall n: int :: 
  { $let#4_k(n) } 
  $let#4$canCall(n) ==> LitInt(0) <= $let#4_k(n) && $let#4_k(n) < n);

implementation Impl$$_module.__default.LetSuchThat2(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;
  var k#0: int;
  var k#0_0: int;
  var k#2: int;

    // AddMethodImpl: LetSuchThat2, Impl$$_module.__default.LetSuchThat2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(697,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(698,15)
    assume true;
    havoc k#0;
    if (true)
    {
    }

    assert ($Is(n#0 - 1, TInt) && n#0 - 1 < n#0)
       || 
      ($Is(LitInt(0), TInt) && 0 < n#0)
       || (exists k#1: int :: k#1 < n#0);
    assume true;
    assume k#0 < n#0;
    assume $let#2$canCall(n#0);
    assume $let#2$canCall(n#0);
    x#0 := (var k#1 := $let#2_k(n#0); k#1) + 3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(698,40)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(699,3)
    assume true;
    assert x#0 < n#0 + 3;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(700,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(701,7)
        assume true;
        havoc k#0_0;
        if (true)
        {
            if (LitInt(0) <= k#0_0)
            {
            }
        }

        assert ($Is(n#0 - 1, TInt) && LitInt(0) <= n#0 - 1 && n#0 - 1 < n#0)
           || 
          ($Is(LitInt(0), TInt) && LitInt(0) <= LitInt(0) && 0 < n#0)
           || 
          ($Is(LitInt(0), TInt) && LitInt(0) <= LitInt(0) && 0 < n#0)
           || (exists k#0_1: int :: LitInt(0) <= k#0_1 && k#0_1 < n#0);
        assume true;
        assume LitInt(0) <= k#0_0 && k#0_0 < n#0;
        assume $let#3$canCall(n#0);
        assume $let#3$canCall(n#0);
        x#0 := (var k#0_1 := $let#3_k(n#0); k#0_1);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(701,31)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(703,7)
        assume true;
        havoc k#2;
        if (LitInt(0) <= k#2)
        {
        }

        assert ($Is(n#0 - 1, Tclass._System.nat()) && n#0 - 1 < n#0)
           || 
          ($Is(LitInt(0), Tclass._System.nat()) && 0 < n#0)
           || 
          ($Is(LitInt(0), Tclass._System.nat()) && 0 < n#0)
           || (exists k#3: int :: LitInt(0) <= k#3 && k#3 < n#0);
        assume LitInt(0) <= k#2;
        assume k#2 < n#0;
        assume $let#4$canCall(n#0);
        assume $let#4$canCall(n#0);
        x#0 := (var k#3 := $let#4_k(n#0); k#3);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(703,31)"} true;
    }
}



procedure CheckWellformed$$_module.__default.LetSuchThat3(n#0: int)
   returns (xx#0: int, 
    yy#0: DatatypeType
       where $Is(yy#0, Tclass._module.Lindgren())
         && $IsAlloc(yy#0, Tclass._module.Lindgren(), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LetSuchThat3(n#0: int)
   returns (xx#0: int, 
    yy#0: DatatypeType
       where $Is(yy#0, Tclass._module.Lindgren())
         && $IsAlloc(yy#0, Tclass._module.Lindgren(), $Heap));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.LetSuchThat3(n#0: int)
   returns (xx#0: int, 
    defass#yy#0: bool, 
    yy#0: DatatypeType
       where defass#yy#0
         ==> $Is(yy#0, Tclass._module.Lindgren())
           && $IsAlloc(yy#0, Tclass._module.Lindgren(), $Heap), 
    $_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



function $let#5_x() : int;

function $let#5$canCall() : bool;

axiom $let#5$canCall() ==> $let#5_x() == LitInt(1);

function $let#6_x() : int;

function $let#6$canCall() : bool;

axiom $let#6$canCall()
   ==> $let#6_x() == LitInt(3) || $let#6_x() == LitInt(7) || $let#6_x() == LitInt(11);

function $let#7_x(n: int) : int;

function $let#7$canCall(n: int) : bool;

axiom (forall n: int :: { $let#7_x(n) } $let#7$canCall(n) ==> $let#7_x(n) == n + 12);

function $let#8_y() : DatatypeType;

function $let#8$canCall() : bool;

axiom $let#8$canCall()
   ==> $Is($let#8_y(), Tclass._module.Lindgren())
     && $let#8_y() == Lit(#_module.Lindgren.HerrNilsson());

function $let#9_y() : DatatypeType;

function $let#9$canCall() : bool;

axiom $let#9$canCall()
   ==> $Is($let#9_y(), Tclass._module.Lindgren())
     && _module.Lindgren#Equal($let#9_y(), $let#9_y());

function $let#10_x() : int;

function $let#10$canCall() : bool;

axiom $let#10$canCall()
   ==> $let#10_x() == LitInt(3)
     || $let#10_x() == LitInt(3)
     || $let#10_x() == LitInt(2)
     || $let#10_x() == LitInt(3);

function $let#11_x() : int;

function $let#11$canCall() : bool;

axiom $let#11$canCall()
   ==> Map#Domain(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(5)), $Box(LitInt(10))), 
      $Box(LitInt(6)), 
      $Box(LitInt(12))))[$Box($let#11_x())];

function $let#12_x(n: int) : int;

function $let#12$canCall(n: int) : bool;

axiom (forall n: int :: 
  { $let#12_x(n) } 
  $let#12$canCall(n)
     ==> Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n)), $Box(n)), $Box(LitInt(2))), 
      $Box($let#12_x(n))));

function $let#13_x() : int;

function $let#13$canCall() : bool;

axiom $let#13$canCall()
   ==> Map#Domain((var m#3 := Lit(Map#Empty(): Map Box Box); m#3))[$Box($let#13_x())];

implementation Impl$$_module.__default.LetSuchThat3(n#0: int)
   returns (xx#0: int, defass#yy#0: bool, yy#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;
  var x#2: int;
  var x#4: int;
  var y#0: DatatypeType;
  var y#2: DatatypeType;
  var x#6: int;
  var x#8: int;
  var x#10: int;
  var x#12: int;
  var m#Z#0: Map Box Box;
  var let#0#0#0: Map Box Box;

    // AddMethodImpl: LetSuchThat3, Impl$$_module.__default.LetSuchThat3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(707,66): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(708,6)
    assume true;
    havoc x#0;
    if (true)
    {
    }

    assert ($Is(LitInt(1), TInt) && LitInt(1) == LitInt(1))
       || 
      ($Is(LitInt(0), TInt) && LitInt(0) == LitInt(1))
       || (exists x#1: int :: x#1 == LitInt(1));
    assume true;
    assume x#0 == LitInt(1);
    assume $let#5$canCall();
    assume $let#5$canCall();
    xx#0 := (var x#1 := $let#5_x(); x#1 + 10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(708,31)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(709,6)
    assume true;
    havoc x#2;
    if (true)
    {
    }

    assert ($Is(LitInt(11), TInt)
         && (LitInt(11) == LitInt(3) || LitInt(11) == LitInt(7) || LitInt(11) == LitInt(11)))
       || 
      ($Is(LitInt(7), TInt)
         && (LitInt(7) == LitInt(3) || LitInt(7) == LitInt(7) || LitInt(7) == LitInt(11)))
       || 
      ($Is(LitInt(3), TInt)
         && (LitInt(3) == LitInt(3) || LitInt(3) == LitInt(7) || LitInt(3) == LitInt(11)))
       || 
      ($Is(LitInt(0), TInt)
         && (LitInt(0) == LitInt(3) || LitInt(0) == LitInt(7) || LitInt(0) == LitInt(11)))
       || (exists x#3: int :: x#3 == LitInt(3) || x#3 == LitInt(7) || x#3 == LitInt(11));
    assume true;
    assume x#2 == LitInt(3) || x#2 == LitInt(7) || x#2 == LitInt(11);
    assume $let#6$canCall();
    assume $let#6$canCall();
    xx#0 := (var x#3 := $let#6_x(); x#3 + 10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(709,38)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(710,6)
    assume true;
    havoc x#4;
    if (true)
    {
    }

    assert ($Is(n#0 + 12, TInt) && n#0 + 12 == n#0 + 12)
       || 
      ($Is(LitInt(0), TInt) && LitInt(0) == n#0 + 12)
       || (exists x#5: int :: x#5 == n#0 + 12);
    assume true;
    assume x#4 == n#0 + 12;
    assume $let#7$canCall(n#0);
    assume $let#7$canCall(n#0);
    xx#0 := (var x#5 := $let#7_x(n#0); x#5 + 10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(710,36)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(711,6)
    assume true;
    havoc y#0;
    if ($Is(y#0, Tclass._module.Lindgren()))
    {
    }

    assert ($Is(Lit(#_module.Lindgren.HerrNilsson()), Tclass._module.Lindgren())
         && Lit(#_module.Lindgren.HerrNilsson()) == Lit(#_module.Lindgren.HerrNilsson()))
       || 
      ($Is(Lit(#_module.Lindgren.HerrNilsson()), Tclass._module.Lindgren())
         && Lit(#_module.Lindgren.HerrNilsson()) == Lit(#_module.Lindgren.HerrNilsson()))
       || (exists y#1: DatatypeType :: 
        $Is(y#1, Tclass._module.Lindgren())
           && y#1 == Lit(#_module.Lindgren.HerrNilsson()));
    assume $Is(y#0, Tclass._module.Lindgren());
    assume y#0 == Lit(#_module.Lindgren.HerrNilsson());
    assume $let#8$canCall();
    assume $let#8$canCall();
    yy#0 := (var y#1 := $let#8_y(); y#1);
    defass#yy#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(711,38)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(712,6)
    assume true;
    havoc y#2;
    if ($Is(y#2, Tclass._module.Lindgren()))
    {
    }

    assert ($Is(Lit(#_module.Lindgren.HerrNilsson()), Tclass._module.Lindgren())
         && _module.Lindgren#Equal(#_module.Lindgren.HerrNilsson(), #_module.Lindgren.HerrNilsson()))
       || (exists y#3: DatatypeType :: 
        $Is(y#3, Tclass._module.Lindgren()) && _module.Lindgren#Equal(y#3, y#3));
    assume $Is(y#2, Tclass._module.Lindgren());
    assume _module.Lindgren#Equal(y#2, y#2);
    assume $let#9$canCall();
    assume $let#9$canCall();
    yy#0 := (var y#3 := $let#9_y(); y#3);
    defass#yy#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(712,26)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(713,6)
    assume true;
    havoc x#6;
    if (true)
    {
    }

    assert ($Is(LitInt(3), TInt)
         && (
          LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(2)
           || LitInt(3) == LitInt(3)))
       || 
      ($Is(LitInt(2), TInt)
         && (
          LitInt(2) == LitInt(3)
           || LitInt(2) == LitInt(3)
           || LitInt(2) == LitInt(2)
           || LitInt(2) == LitInt(3)))
       || 
      ($Is(LitInt(3), TInt)
         && (
          LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(2)
           || LitInt(3) == LitInt(3)))
       || 
      ($Is(LitInt(3), TInt)
         && (
          LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(3)
           || LitInt(3) == LitInt(2)
           || LitInt(3) == LitInt(3)))
       || 
      ($Is(LitInt(0), TInt)
         && (
          LitInt(0) == LitInt(3)
           || LitInt(0) == LitInt(3)
           || LitInt(0) == LitInt(2)
           || LitInt(0) == LitInt(3)))
       || (exists x#7: int :: 
        x#7 == LitInt(3) || x#7 == LitInt(3) || x#7 == LitInt(2) || x#7 == LitInt(3));
    assume true;
    assume x#6 == LitInt(3) || x#6 == LitInt(3) || x#6 == LitInt(2) || x#6 == LitInt(3);
    assume $let#10$canCall();
    assume $let#10$canCall();
    xx#0 := (var x#7 := $let#10_x(); x#7 + 10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(713,48)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(714,6)
    assume true;
    havoc x#8;
    if (true)
    {
    }

    assert ($Is(LitInt(0), TInt)
         && Map#Domain(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(5)), $Box(LitInt(10))), 
            $Box(LitInt(6)), 
            $Box(LitInt(12))))[$Box(0)])
       || (exists x#9: int :: 
        Map#Domain(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(5)), $Box(LitInt(10))), 
            $Box(LitInt(6)), 
            $Box(LitInt(12))))[$Box(x#9)]);
    assume true;
    assume Map#Domain(Map#Build(Map#Build(Map#Empty(): Map Box Box, $Box(LitInt(5)), $Box(LitInt(10))), 
        $Box(LitInt(6)), 
        $Box(LitInt(12))))[$Box(x#8)];
    assume $let#11$canCall();
    assume $let#11$canCall();
    xx#0 := (var x#9 := $let#11_x(); x#9 + 10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(714,49)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(715,6)
    assume true;
    havoc x#10;
    if (true)
    {
    }

    assert ($Is(LitInt(2), TInt)
         && Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(2)))
       || 
      ($Is(n#0, TInt)
         && Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(n#0)))
       || 
      ($Is(n#0, TInt)
         && Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(n#0)))
       || 
      ($Is(LitInt(0), TInt)
         && Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(0)))
       || (exists x#11: int :: 
        Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
            $Box(LitInt(2))), 
          $Box(x#11)));
    assume true;
    assume Seq#Contains(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(n#0)), $Box(n#0)), 
        $Box(LitInt(2))), 
      $Box(x#10));
    assume $let#12$canCall(n#0);
    assume $let#12$canCall(n#0);
    xx#0 := (var x#11 := $let#12_x(n#0); x#11 + 10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(715,37)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(716,6)
    assume true;
    havoc x#12;
    if (true)
    {
        havoc m#Z#0;
        assume $Is(m#Z#0, TMap(TInt, TInt));
        assume let#0#0#0 == Lit(Map#Empty(): Map Box Box);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, TMap(TInt, TInt));
        assume m#Z#0 == let#0#0#0;
    }

    assert ($Is(LitInt(0), TInt)
         && Map#Domain((var m#1 := Lit(Map#Empty(): Map Box Box); m#1))[$Box(0)])
       || (exists x#13: int :: 
        Map#Domain((var m#0 := Lit(Map#Empty(): Map Box Box); m#0))[$Box(x#13)]);
    assume true;
    assume Map#Domain((var m#2 := Lit(Map#Empty(): Map Box Box); m#2))[$Box(x#12)];
    assume $let#13$canCall();
    assume $let#13$canCall();
    xx#0 := (var x#13 := $let#13_x(); x#13 + 10);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/SmallTests.dfy(716,62)"} true;
    assert defass#yy#0;
}



const unique class.GenericPick.__default: ClassName;

function Tclass.GenericPick.__default() : Ty;

const unique Tagclass.GenericPick.__default: TyTag;

// Tclass.GenericPick.__default Tag
axiom Tag(Tclass.GenericPick.__default()) == Tagclass.GenericPick.__default
   && TagFamily(Tclass.GenericPick.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.GenericPick.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.GenericPick.__default()) } 
  $IsBox(bx, Tclass.GenericPick.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.GenericPick.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.GenericPick.__default()) } 
  $Is($o, Tclass.GenericPick.__default())
     <==> $o == null || dtype($o) == Tclass.GenericPick.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.GenericPick.__default(), $h) } 
  $IsAlloc($o, Tclass.GenericPick.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for GenericPick._default.SetPick0
function GenericPick.__default.SetPick0(GenericPick._default.SetPick0$U: Ty, s#0: Set Box) : Box;

function GenericPick.__default.SetPick0#canCall(GenericPick._default.SetPick0$U: Ty, s#0: Set Box) : bool;

// consequence axiom for GenericPick.__default.SetPick0
axiom true
   ==> (forall GenericPick._default.SetPick0$U: Ty, s#0: Set Box :: 
    { GenericPick.__default.SetPick0(GenericPick._default.SetPick0$U, s#0) } 
    GenericPick.__default.SetPick0#canCall(GenericPick._default.SetPick0$U, s#0)
         || ($Is(s#0, TSet(GenericPick._default.SetPick0$U))
           && !Set#Equal(s#0, Set#Empty(): Set Box))
       ==> $IsBox(GenericPick.__default.SetPick0(GenericPick._default.SetPick0$U, s#0), 
        GenericPick._default.SetPick0$U));

function GenericPick.__default.SetPick0#requires(Ty, Set Box) : bool;

// #requires axiom for GenericPick.__default.SetPick0
axiom (forall GenericPick._default.SetPick0$U: Ty, $Heap: Heap, s#0: Set Box :: 
  { GenericPick.__default.SetPick0#requires(GenericPick._default.SetPick0$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TSet(GenericPick._default.SetPick0$U))
     ==> GenericPick.__default.SetPick0#requires(GenericPick._default.SetPick0$U, s#0)
       == !Set#Equal(s#0, Set#Empty(): Set Box));

function $let#14_x(GenericPick._default.SetPick0$U: Ty, s: Set Box) : Box;

function $let#14$canCall(GenericPick._default.SetPick0$U: Ty, s: Set Box) : bool;

axiom (forall GenericPick._default.SetPick0$U: Ty, s: Set Box :: 
  { $let#14_x(GenericPick._default.SetPick0$U, s) } 
  $let#14$canCall(GenericPick._default.SetPick0$U, s)
     ==> s[$let#14_x(GenericPick._default.SetPick0$U, s)]);

// definition axiom for GenericPick.__default.SetPick0 (revealed)
axiom true
   ==> (forall GenericPick._default.SetPick0$U: Ty, $Heap: Heap, s#0: Set Box :: 
    { GenericPick.__default.SetPick0(GenericPick._default.SetPick0$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.SetPick0#canCall(GenericPick._default.SetPick0$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSet(GenericPick._default.SetPick0$U))
           && !Set#Equal(s#0, Set#Empty(): Set Box))
       ==> $let#14$canCall(GenericPick._default.SetPick0$U, s#0)
         && GenericPick.__default.SetPick0(GenericPick._default.SetPick0$U, s#0)
           == (var x#4 := $let#14_x(GenericPick._default.SetPick0$U, s#0); x#4));

// definition axiom for GenericPick.__default.SetPick0 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.SetPick0$U: Ty, $Heap: Heap, s#0: Set Box :: 
    {:weight 3} { GenericPick.__default.SetPick0(GenericPick._default.SetPick0$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.SetPick0#canCall(GenericPick._default.SetPick0$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSet(GenericPick._default.SetPick0$U))
           && !Set#Equal(s#0, Set#Empty(): Set Box))
       ==> $let#14$canCall(GenericPick._default.SetPick0$U, Lit(s#0))
         && GenericPick.__default.SetPick0(GenericPick._default.SetPick0$U, Lit(s#0))
           == (var x#5 := $let#14_x(GenericPick._default.SetPick0$U, Lit(s#0)); x#5));

// function declaration for GenericPick._default.SetPick1
function GenericPick.__default.SetPick1(GenericPick._default.SetPick1$U: Ty, s#0: Set Box) : Box;

function GenericPick.__default.SetPick1#canCall(GenericPick._default.SetPick1$U: Ty, s#0: Set Box) : bool;

// consequence axiom for GenericPick.__default.SetPick1
axiom true
   ==> (forall GenericPick._default.SetPick1$U: Ty, s#0: Set Box :: 
    { GenericPick.__default.SetPick1(GenericPick._default.SetPick1$U, s#0) } 
    GenericPick.__default.SetPick1#canCall(GenericPick._default.SetPick1$U, s#0)
         || ($Is(s#0, TSet(GenericPick._default.SetPick1$U)) && Set#Card(s#0) != 0)
       ==> $IsBox(GenericPick.__default.SetPick1(GenericPick._default.SetPick1$U, s#0), 
        GenericPick._default.SetPick1$U));

function GenericPick.__default.SetPick1#requires(Ty, Set Box) : bool;

// #requires axiom for GenericPick.__default.SetPick1
axiom (forall GenericPick._default.SetPick1$U: Ty, $Heap: Heap, s#0: Set Box :: 
  { GenericPick.__default.SetPick1#requires(GenericPick._default.SetPick1$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TSet(GenericPick._default.SetPick1$U))
     ==> GenericPick.__default.SetPick1#requires(GenericPick._default.SetPick1$U, s#0)
       == (Set#Card(s#0) != 0));

function $let#17_x(GenericPick._default.SetPick1$U: Ty, s: Set Box) : Box;

function $let#17$canCall(GenericPick._default.SetPick1$U: Ty, s: Set Box) : bool;

axiom (forall GenericPick._default.SetPick1$U: Ty, s: Set Box :: 
  { $let#17_x(GenericPick._default.SetPick1$U, s) } 
  $let#17$canCall(GenericPick._default.SetPick1$U, s)
     ==> s[$let#17_x(GenericPick._default.SetPick1$U, s)]);

// definition axiom for GenericPick.__default.SetPick1 (revealed)
axiom true
   ==> (forall GenericPick._default.SetPick1$U: Ty, $Heap: Heap, s#0: Set Box :: 
    { GenericPick.__default.SetPick1(GenericPick._default.SetPick1$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.SetPick1#canCall(GenericPick._default.SetPick1$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSet(GenericPick._default.SetPick1$U))
           && Set#Card(s#0) != 0)
       ==> $let#17$canCall(GenericPick._default.SetPick1$U, s#0)
         && GenericPick.__default.SetPick1(GenericPick._default.SetPick1$U, s#0)
           == (var x#4 := $let#17_x(GenericPick._default.SetPick1$U, s#0); x#4));

// definition axiom for GenericPick.__default.SetPick1 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.SetPick1$U: Ty, $Heap: Heap, s#0: Set Box :: 
    {:weight 3} { GenericPick.__default.SetPick1(GenericPick._default.SetPick1$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.SetPick1#canCall(GenericPick._default.SetPick1$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSet(GenericPick._default.SetPick1$U))
           && Set#Card(Lit(s#0)) != 0)
       ==> $let#17$canCall(GenericPick._default.SetPick1$U, Lit(s#0))
         && GenericPick.__default.SetPick1(GenericPick._default.SetPick1$U, Lit(s#0))
           == (var x#5 := $let#17_x(GenericPick._default.SetPick1$U, Lit(s#0)); x#5));

// function declaration for GenericPick._default.SetPick2
function GenericPick.__default.SetPick2(GenericPick._default.SetPick2$U: Ty, s#0: Set Box) : Box;

function GenericPick.__default.SetPick2#canCall(GenericPick._default.SetPick2$U: Ty, s#0: Set Box) : bool;

// consequence axiom for GenericPick.__default.SetPick2
axiom true
   ==> (forall GenericPick._default.SetPick2$U: Ty, s#0: Set Box :: 
    { GenericPick.__default.SetPick2(GenericPick._default.SetPick2$U, s#0) } 
    GenericPick.__default.SetPick2#canCall(GenericPick._default.SetPick2$U, s#0)
         || ($Is(s#0, TSet(GenericPick._default.SetPick2$U))
           && (exists x#8: Box :: 
            { s#0[x#8] } 
            $IsBox(x#8, GenericPick._default.SetPick2$U) && s#0[x#8]))
       ==> $IsBox(GenericPick.__default.SetPick2(GenericPick._default.SetPick2$U, s#0), 
        GenericPick._default.SetPick2$U));

function GenericPick.__default.SetPick2#requires(Ty, Set Box) : bool;

// #requires axiom for GenericPick.__default.SetPick2
axiom (forall GenericPick._default.SetPick2$U: Ty, $Heap: Heap, s#0: Set Box :: 
  { GenericPick.__default.SetPick2#requires(GenericPick._default.SetPick2$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TSet(GenericPick._default.SetPick2$U))
     ==> GenericPick.__default.SetPick2#requires(GenericPick._default.SetPick2$U, s#0)
       == (exists x#9: Box :: 
        { s#0[x#9] } 
        $IsBox(x#9, GenericPick._default.SetPick2$U) && s#0[x#9]));

function $let#20_x(GenericPick._default.SetPick2$U: Ty, s: Set Box) : Box;

function $let#20$canCall(GenericPick._default.SetPick2$U: Ty, s: Set Box) : bool;

axiom (forall GenericPick._default.SetPick2$U: Ty, s: Set Box :: 
  { $let#20_x(GenericPick._default.SetPick2$U, s) } 
  $let#20$canCall(GenericPick._default.SetPick2$U, s)
     ==> s[$let#20_x(GenericPick._default.SetPick2$U, s)]);

// definition axiom for GenericPick.__default.SetPick2 (revealed)
axiom true
   ==> (forall GenericPick._default.SetPick2$U: Ty, $Heap: Heap, s#0: Set Box :: 
    { GenericPick.__default.SetPick2(GenericPick._default.SetPick2$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.SetPick2#canCall(GenericPick._default.SetPick2$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSet(GenericPick._default.SetPick2$U))
           && (exists x#9: Box :: 
            { s#0[x#9] } 
            $IsBox(x#9, GenericPick._default.SetPick2$U) && s#0[x#9]))
       ==> $let#20$canCall(GenericPick._default.SetPick2$U, s#0)
         && GenericPick.__default.SetPick2(GenericPick._default.SetPick2$U, s#0)
           == (var x#10 := $let#20_x(GenericPick._default.SetPick2$U, s#0); x#10));

// definition axiom for GenericPick.__default.SetPick2 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.SetPick2$U: Ty, $Heap: Heap, s#0: Set Box :: 
    {:weight 3} { GenericPick.__default.SetPick2(GenericPick._default.SetPick2$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.SetPick2#canCall(GenericPick._default.SetPick2$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSet(GenericPick._default.SetPick2$U))
           && (exists x#11: Box :: 
            { s#0[x#11] } 
            $IsBox(x#11, GenericPick._default.SetPick2$U) && Lit(s#0)[x#11]))
       ==> $let#20$canCall(GenericPick._default.SetPick2$U, Lit(s#0))
         && GenericPick.__default.SetPick2(GenericPick._default.SetPick2$U, Lit(s#0))
           == (var x#12 := $let#20_x(GenericPick._default.SetPick2$U, Lit(s#0)); x#12));

// function declaration for GenericPick._default.MultisetPick0
function GenericPick.__default.MultisetPick0(GenericPick._default.MultisetPick0$U: Ty, s#0: MultiSet Box) : Box;

function GenericPick.__default.MultisetPick0#canCall(GenericPick._default.MultisetPick0$U: Ty, s#0: MultiSet Box) : bool;

// consequence axiom for GenericPick.__default.MultisetPick0
axiom true
   ==> (forall GenericPick._default.MultisetPick0$U: Ty, s#0: MultiSet Box :: 
    { GenericPick.__default.MultisetPick0(GenericPick._default.MultisetPick0$U, s#0) } 
    GenericPick.__default.MultisetPick0#canCall(GenericPick._default.MultisetPick0$U, s#0)
         || ($Is(s#0, TMultiSet(GenericPick._default.MultisetPick0$U))
           && !MultiSet#Equal(s#0, MultiSet#Empty(): MultiSet Box))
       ==> $IsBox(GenericPick.__default.MultisetPick0(GenericPick._default.MultisetPick0$U, s#0), 
        GenericPick._default.MultisetPick0$U));

function GenericPick.__default.MultisetPick0#requires(Ty, MultiSet Box) : bool;

// #requires axiom for GenericPick.__default.MultisetPick0
axiom (forall GenericPick._default.MultisetPick0$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
  { GenericPick.__default.MultisetPick0#requires(GenericPick._default.MultisetPick0$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick0$U))
     ==> GenericPick.__default.MultisetPick0#requires(GenericPick._default.MultisetPick0$U, s#0)
       == !MultiSet#Equal(s#0, MultiSet#Empty(): MultiSet Box));

function $let#23_x(GenericPick._default.MultisetPick0$U: Ty, s: MultiSet Box) : Box;

function $let#23$canCall(GenericPick._default.MultisetPick0$U: Ty, s: MultiSet Box) : bool;

axiom (forall GenericPick._default.MultisetPick0$U: Ty, s: MultiSet Box :: 
  { $let#23_x(GenericPick._default.MultisetPick0$U, s) } 
  $let#23$canCall(GenericPick._default.MultisetPick0$U, s)
     ==> s[$let#23_x(GenericPick._default.MultisetPick0$U, s)] > 0);

// definition axiom for GenericPick.__default.MultisetPick0 (revealed)
axiom true
   ==> (forall GenericPick._default.MultisetPick0$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
    { GenericPick.__default.MultisetPick0(GenericPick._default.MultisetPick0$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.MultisetPick0#canCall(GenericPick._default.MultisetPick0$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick0$U))
           && !MultiSet#Equal(s#0, MultiSet#Empty(): MultiSet Box))
       ==> $let#23$canCall(GenericPick._default.MultisetPick0$U, s#0)
         && GenericPick.__default.MultisetPick0(GenericPick._default.MultisetPick0$U, s#0)
           == (var x#4 := $let#23_x(GenericPick._default.MultisetPick0$U, s#0); x#4));

// definition axiom for GenericPick.__default.MultisetPick0 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.MultisetPick0$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
    {:weight 3} { GenericPick.__default.MultisetPick0(GenericPick._default.MultisetPick0$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.MultisetPick0#canCall(GenericPick._default.MultisetPick0$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick0$U))
           && !MultiSet#Equal(s#0, MultiSet#Empty(): MultiSet Box))
       ==> $let#23$canCall(GenericPick._default.MultisetPick0$U, Lit(s#0))
         && GenericPick.__default.MultisetPick0(GenericPick._default.MultisetPick0$U, Lit(s#0))
           == (var x#5 := $let#23_x(GenericPick._default.MultisetPick0$U, Lit(s#0)); x#5));

// function declaration for GenericPick._default.MultisetPick1
function GenericPick.__default.MultisetPick1(GenericPick._default.MultisetPick1$U: Ty, s#0: MultiSet Box) : Box;

function GenericPick.__default.MultisetPick1#canCall(GenericPick._default.MultisetPick1$U: Ty, s#0: MultiSet Box) : bool;

// consequence axiom for GenericPick.__default.MultisetPick1
axiom true
   ==> (forall GenericPick._default.MultisetPick1$U: Ty, s#0: MultiSet Box :: 
    { GenericPick.__default.MultisetPick1(GenericPick._default.MultisetPick1$U, s#0) } 
    GenericPick.__default.MultisetPick1#canCall(GenericPick._default.MultisetPick1$U, s#0)
         || ($Is(s#0, TMultiSet(GenericPick._default.MultisetPick1$U))
           && MultiSet#Card(s#0) != 0)
       ==> $IsBox(GenericPick.__default.MultisetPick1(GenericPick._default.MultisetPick1$U, s#0), 
        GenericPick._default.MultisetPick1$U));

function GenericPick.__default.MultisetPick1#requires(Ty, MultiSet Box) : bool;

// #requires axiom for GenericPick.__default.MultisetPick1
axiom (forall GenericPick._default.MultisetPick1$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
  { GenericPick.__default.MultisetPick1#requires(GenericPick._default.MultisetPick1$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick1$U))
     ==> GenericPick.__default.MultisetPick1#requires(GenericPick._default.MultisetPick1$U, s#0)
       == (MultiSet#Card(s#0) != 0));

function $let#26_x(GenericPick._default.MultisetPick1$U: Ty, s: MultiSet Box) : Box;

function $let#26$canCall(GenericPick._default.MultisetPick1$U: Ty, s: MultiSet Box) : bool;

axiom (forall GenericPick._default.MultisetPick1$U: Ty, s: MultiSet Box :: 
  { $let#26_x(GenericPick._default.MultisetPick1$U, s) } 
  $let#26$canCall(GenericPick._default.MultisetPick1$U, s)
     ==> s[$let#26_x(GenericPick._default.MultisetPick1$U, s)] > 0);

// definition axiom for GenericPick.__default.MultisetPick1 (revealed)
axiom true
   ==> (forall GenericPick._default.MultisetPick1$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
    { GenericPick.__default.MultisetPick1(GenericPick._default.MultisetPick1$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.MultisetPick1#canCall(GenericPick._default.MultisetPick1$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick1$U))
           && MultiSet#Card(s#0) != 0)
       ==> $let#26$canCall(GenericPick._default.MultisetPick1$U, s#0)
         && GenericPick.__default.MultisetPick1(GenericPick._default.MultisetPick1$U, s#0)
           == (var x#4 := $let#26_x(GenericPick._default.MultisetPick1$U, s#0); x#4));

// definition axiom for GenericPick.__default.MultisetPick1 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.MultisetPick1$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
    {:weight 3} { GenericPick.__default.MultisetPick1(GenericPick._default.MultisetPick1$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.MultisetPick1#canCall(GenericPick._default.MultisetPick1$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick1$U))
           && MultiSet#Card(Lit(s#0)) != 0)
       ==> $let#26$canCall(GenericPick._default.MultisetPick1$U, Lit(s#0))
         && GenericPick.__default.MultisetPick1(GenericPick._default.MultisetPick1$U, Lit(s#0))
           == (var x#5 := $let#26_x(GenericPick._default.MultisetPick1$U, Lit(s#0)); x#5));

// function declaration for GenericPick._default.MultisetPick2
function GenericPick.__default.MultisetPick2(GenericPick._default.MultisetPick2$U: Ty, s#0: MultiSet Box) : Box;

function GenericPick.__default.MultisetPick2#canCall(GenericPick._default.MultisetPick2$U: Ty, s#0: MultiSet Box) : bool;

// consequence axiom for GenericPick.__default.MultisetPick2
axiom true
   ==> (forall GenericPick._default.MultisetPick2$U: Ty, s#0: MultiSet Box :: 
    { GenericPick.__default.MultisetPick2(GenericPick._default.MultisetPick2$U, s#0) } 
    GenericPick.__default.MultisetPick2#canCall(GenericPick._default.MultisetPick2$U, s#0)
         || ($Is(s#0, TMultiSet(GenericPick._default.MultisetPick2$U))
           && (exists x#8: Box :: 
            { s#0[x#8] } 
            $IsBox(x#8, GenericPick._default.MultisetPick2$U) && s#0[x#8] > 0))
       ==> $IsBox(GenericPick.__default.MultisetPick2(GenericPick._default.MultisetPick2$U, s#0), 
        GenericPick._default.MultisetPick2$U));

function GenericPick.__default.MultisetPick2#requires(Ty, MultiSet Box) : bool;

// #requires axiom for GenericPick.__default.MultisetPick2
axiom (forall GenericPick._default.MultisetPick2$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
  { GenericPick.__default.MultisetPick2#requires(GenericPick._default.MultisetPick2$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick2$U))
     ==> GenericPick.__default.MultisetPick2#requires(GenericPick._default.MultisetPick2$U, s#0)
       == (exists x#9: Box :: 
        { s#0[x#9] } 
        $IsBox(x#9, GenericPick._default.MultisetPick2$U) && s#0[x#9] > 0));

function $let#29_x(GenericPick._default.MultisetPick2$U: Ty, s: MultiSet Box) : Box;

function $let#29$canCall(GenericPick._default.MultisetPick2$U: Ty, s: MultiSet Box) : bool;

axiom (forall GenericPick._default.MultisetPick2$U: Ty, s: MultiSet Box :: 
  { $let#29_x(GenericPick._default.MultisetPick2$U, s) } 
  $let#29$canCall(GenericPick._default.MultisetPick2$U, s)
     ==> s[$let#29_x(GenericPick._default.MultisetPick2$U, s)] > 0);

// definition axiom for GenericPick.__default.MultisetPick2 (revealed)
axiom true
   ==> (forall GenericPick._default.MultisetPick2$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
    { GenericPick.__default.MultisetPick2(GenericPick._default.MultisetPick2$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.MultisetPick2#canCall(GenericPick._default.MultisetPick2$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick2$U))
           && (exists x#9: Box :: 
            { s#0[x#9] } 
            $IsBox(x#9, GenericPick._default.MultisetPick2$U) && s#0[x#9] > 0))
       ==> $let#29$canCall(GenericPick._default.MultisetPick2$U, s#0)
         && GenericPick.__default.MultisetPick2(GenericPick._default.MultisetPick2$U, s#0)
           == (var x#10 := $let#29_x(GenericPick._default.MultisetPick2$U, s#0); x#10));

// definition axiom for GenericPick.__default.MultisetPick2 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.MultisetPick2$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
    {:weight 3} { GenericPick.__default.MultisetPick2(GenericPick._default.MultisetPick2$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.MultisetPick2#canCall(GenericPick._default.MultisetPick2$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick2$U))
           && (exists x#11: Box :: 
            { s#0[x#11] } 
            $IsBox(x#11, GenericPick._default.MultisetPick2$U) && Lit(s#0)[x#11] > 0))
       ==> $let#29$canCall(GenericPick._default.MultisetPick2$U, Lit(s#0))
         && GenericPick.__default.MultisetPick2(GenericPick._default.MultisetPick2$U, Lit(s#0))
           == (var x#12 := $let#29_x(GenericPick._default.MultisetPick2$U, Lit(s#0)); x#12));

// function declaration for GenericPick._default.MultisetPick3
function GenericPick.__default.MultisetPick3(GenericPick._default.MultisetPick3$U: Ty, s#0: MultiSet Box) : Box;

function GenericPick.__default.MultisetPick3#canCall(GenericPick._default.MultisetPick3$U: Ty, s#0: MultiSet Box) : bool;

// consequence axiom for GenericPick.__default.MultisetPick3
axiom true
   ==> (forall GenericPick._default.MultisetPick3$U: Ty, s#0: MultiSet Box :: 
    { GenericPick.__default.MultisetPick3(GenericPick._default.MultisetPick3$U, s#0) } 
    GenericPick.__default.MultisetPick3#canCall(GenericPick._default.MultisetPick3$U, s#0)
         || ($Is(s#0, TMultiSet(GenericPick._default.MultisetPick3$U))
           && (exists x#8: Box :: 
            { s#0[x#8] } 
            $IsBox(x#8, GenericPick._default.MultisetPick3$U)
               && 
              s#0[x#8] > 0
               && s#0[x#8] > 0))
       ==> $IsBox(GenericPick.__default.MultisetPick3(GenericPick._default.MultisetPick3$U, s#0), 
        GenericPick._default.MultisetPick3$U));

function GenericPick.__default.MultisetPick3#requires(Ty, MultiSet Box) : bool;

// #requires axiom for GenericPick.__default.MultisetPick3
axiom (forall GenericPick._default.MultisetPick3$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
  { GenericPick.__default.MultisetPick3#requires(GenericPick._default.MultisetPick3$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick3$U))
     ==> GenericPick.__default.MultisetPick3#requires(GenericPick._default.MultisetPick3$U, s#0)
       == (exists x#9: Box :: 
        { s#0[x#9] } 
        $IsBox(x#9, GenericPick._default.MultisetPick3$U)
           && 
          s#0[x#9] > 0
           && s#0[x#9] > 0));

function $let#32_x(GenericPick._default.MultisetPick3$U: Ty, s: MultiSet Box) : Box;

function $let#32$canCall(GenericPick._default.MultisetPick3$U: Ty, s: MultiSet Box) : bool;

axiom (forall GenericPick._default.MultisetPick3$U: Ty, s: MultiSet Box :: 
  { $let#32_x(GenericPick._default.MultisetPick3$U, s) } 
  $let#32$canCall(GenericPick._default.MultisetPick3$U, s)
     ==> s[$let#32_x(GenericPick._default.MultisetPick3$U, s)] > 0);

// definition axiom for GenericPick.__default.MultisetPick3 (revealed)
axiom true
   ==> (forall GenericPick._default.MultisetPick3$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
    { GenericPick.__default.MultisetPick3(GenericPick._default.MultisetPick3$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.MultisetPick3#canCall(GenericPick._default.MultisetPick3$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick3$U))
           && (exists x#9: Box :: 
            { s#0[x#9] } 
            $IsBox(x#9, GenericPick._default.MultisetPick3$U)
               && 
              s#0[x#9] > 0
               && s#0[x#9] > 0))
       ==> $let#32$canCall(GenericPick._default.MultisetPick3$U, s#0)
         && GenericPick.__default.MultisetPick3(GenericPick._default.MultisetPick3$U, s#0)
           == (var x#10 := $let#32_x(GenericPick._default.MultisetPick3$U, s#0); x#10));

// definition axiom for GenericPick.__default.MultisetPick3 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.MultisetPick3$U: Ty, $Heap: Heap, s#0: MultiSet Box :: 
    {:weight 3} { GenericPick.__default.MultisetPick3(GenericPick._default.MultisetPick3$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.MultisetPick3#canCall(GenericPick._default.MultisetPick3$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TMultiSet(GenericPick._default.MultisetPick3$U))
           && (exists x#11: Box :: 
            { s#0[x#11] } 
            $IsBox(x#11, GenericPick._default.MultisetPick3$U)
               && 
              Lit(s#0)[x#11] > 0
               && Lit(s#0)[x#11] > 0))
       ==> $let#32$canCall(GenericPick._default.MultisetPick3$U, Lit(s#0))
         && GenericPick.__default.MultisetPick3(GenericPick._default.MultisetPick3$U, Lit(s#0))
           == (var x#12 := $let#32_x(GenericPick._default.MultisetPick3$U, Lit(s#0)); x#12));

// function declaration for GenericPick._default.SeqPick0
function GenericPick.__default.SeqPick0(GenericPick._default.SeqPick0$U: Ty, s#0: Seq Box) : Box;

function GenericPick.__default.SeqPick0#canCall(GenericPick._default.SeqPick0$U: Ty, s#0: Seq Box) : bool;

// consequence axiom for GenericPick.__default.SeqPick0
axiom true
   ==> (forall GenericPick._default.SeqPick0$U: Ty, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick0(GenericPick._default.SeqPick0$U, s#0) } 
    GenericPick.__default.SeqPick0#canCall(GenericPick._default.SeqPick0$U, s#0)
         || ($Is(s#0, TSeq(GenericPick._default.SeqPick0$U))
           && !Seq#Equal(s#0, Seq#Empty(): Seq Box))
       ==> $IsBox(GenericPick.__default.SeqPick0(GenericPick._default.SeqPick0$U, s#0), 
        GenericPick._default.SeqPick0$U));

function GenericPick.__default.SeqPick0#requires(Ty, Seq Box) : bool;

// #requires axiom for GenericPick.__default.SeqPick0
axiom (forall GenericPick._default.SeqPick0$U: Ty, $Heap: Heap, s#0: Seq Box :: 
  { GenericPick.__default.SeqPick0#requires(GenericPick._default.SeqPick0$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TSeq(GenericPick._default.SeqPick0$U))
     ==> GenericPick.__default.SeqPick0#requires(GenericPick._default.SeqPick0$U, s#0)
       == !Seq#Equal(s#0, Seq#Empty(): Seq Box));

function $let#35_x(GenericPick._default.SeqPick0$U: Ty, s: Seq Box) : Box;

function $let#35$canCall(GenericPick._default.SeqPick0$U: Ty, s: Seq Box) : bool;

axiom (forall GenericPick._default.SeqPick0$U: Ty, s: Seq Box :: 
  { $let#35_x(GenericPick._default.SeqPick0$U, s) } 
  $let#35$canCall(GenericPick._default.SeqPick0$U, s)
     ==> Seq#Contains(s, $let#35_x(GenericPick._default.SeqPick0$U, s)));

// definition axiom for GenericPick.__default.SeqPick0 (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick0$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick0(GenericPick._default.SeqPick0$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick0#canCall(GenericPick._default.SeqPick0$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick0$U))
           && !Seq#Equal(s#0, Seq#Empty(): Seq Box))
       ==> $let#35$canCall(GenericPick._default.SeqPick0$U, s#0)
         && GenericPick.__default.SeqPick0(GenericPick._default.SeqPick0$U, s#0)
           == (var x#4 := $let#35_x(GenericPick._default.SeqPick0$U, s#0); x#4));

// definition axiom for GenericPick.__default.SeqPick0 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick0$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    {:weight 3} { GenericPick.__default.SeqPick0(GenericPick._default.SeqPick0$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick0#canCall(GenericPick._default.SeqPick0$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick0$U))
           && !Seq#Equal(s#0, Seq#Empty(): Seq Box))
       ==> $let#35$canCall(GenericPick._default.SeqPick0$U, Lit(s#0))
         && GenericPick.__default.SeqPick0(GenericPick._default.SeqPick0$U, Lit(s#0))
           == (var x#5 := $let#35_x(GenericPick._default.SeqPick0$U, Lit(s#0)); x#5));

// function declaration for GenericPick._default.SeqPick1
function GenericPick.__default.SeqPick1(GenericPick._default.SeqPick1$U: Ty, s#0: Seq Box) : Box;

function GenericPick.__default.SeqPick1#canCall(GenericPick._default.SeqPick1$U: Ty, s#0: Seq Box) : bool;

// consequence axiom for GenericPick.__default.SeqPick1
axiom true
   ==> (forall GenericPick._default.SeqPick1$U: Ty, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick1(GenericPick._default.SeqPick1$U, s#0) } 
    GenericPick.__default.SeqPick1#canCall(GenericPick._default.SeqPick1$U, s#0)
         || ($Is(s#0, TSeq(GenericPick._default.SeqPick1$U)) && Seq#Length(s#0) != 0)
       ==> $IsBox(GenericPick.__default.SeqPick1(GenericPick._default.SeqPick1$U, s#0), 
        GenericPick._default.SeqPick1$U));

function GenericPick.__default.SeqPick1#requires(Ty, Seq Box) : bool;

// #requires axiom for GenericPick.__default.SeqPick1
axiom (forall GenericPick._default.SeqPick1$U: Ty, $Heap: Heap, s#0: Seq Box :: 
  { GenericPick.__default.SeqPick1#requires(GenericPick._default.SeqPick1$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TSeq(GenericPick._default.SeqPick1$U))
     ==> GenericPick.__default.SeqPick1#requires(GenericPick._default.SeqPick1$U, s#0)
       == (Seq#Length(s#0) != 0));

function $let#38_x(GenericPick._default.SeqPick1$U: Ty, s: Seq Box) : Box;

function $let#38$canCall(GenericPick._default.SeqPick1$U: Ty, s: Seq Box) : bool;

axiom (forall GenericPick._default.SeqPick1$U: Ty, s: Seq Box :: 
  { $let#38_x(GenericPick._default.SeqPick1$U, s) } 
  $let#38$canCall(GenericPick._default.SeqPick1$U, s)
     ==> Seq#Contains(s, $let#38_x(GenericPick._default.SeqPick1$U, s)));

// definition axiom for GenericPick.__default.SeqPick1 (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick1$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick1(GenericPick._default.SeqPick1$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick1#canCall(GenericPick._default.SeqPick1$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick1$U))
           && Seq#Length(s#0) != 0)
       ==> $let#38$canCall(GenericPick._default.SeqPick1$U, s#0)
         && GenericPick.__default.SeqPick1(GenericPick._default.SeqPick1$U, s#0)
           == (var x#4 := $let#38_x(GenericPick._default.SeqPick1$U, s#0); x#4));

// definition axiom for GenericPick.__default.SeqPick1 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick1$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    {:weight 3} { GenericPick.__default.SeqPick1(GenericPick._default.SeqPick1$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick1#canCall(GenericPick._default.SeqPick1$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick1$U))
           && Seq#Length(Lit(s#0)) != 0)
       ==> $let#38$canCall(GenericPick._default.SeqPick1$U, Lit(s#0))
         && GenericPick.__default.SeqPick1(GenericPick._default.SeqPick1$U, Lit(s#0))
           == (var x#5 := $let#38_x(GenericPick._default.SeqPick1$U, Lit(s#0)); x#5));

// function declaration for GenericPick._default.SeqPick2
function GenericPick.__default.SeqPick2(GenericPick._default.SeqPick2$U: Ty, s#0: Seq Box) : Box;

function GenericPick.__default.SeqPick2#canCall(GenericPick._default.SeqPick2$U: Ty, s#0: Seq Box) : bool;

// consequence axiom for GenericPick.__default.SeqPick2
axiom true
   ==> (forall GenericPick._default.SeqPick2$U: Ty, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick2(GenericPick._default.SeqPick2$U, s#0) } 
    GenericPick.__default.SeqPick2#canCall(GenericPick._default.SeqPick2$U, s#0)
         || ($Is(s#0, TSeq(GenericPick._default.SeqPick2$U))
           && (exists x#8: Box :: 
            { Seq#Contains(s#0, x#8) } 
            $IsBox(x#8, GenericPick._default.SeqPick2$U) && Seq#Contains(s#0, x#8)))
       ==> $IsBox(GenericPick.__default.SeqPick2(GenericPick._default.SeqPick2$U, s#0), 
        GenericPick._default.SeqPick2$U));

function GenericPick.__default.SeqPick2#requires(Ty, Seq Box) : bool;

// #requires axiom for GenericPick.__default.SeqPick2
axiom (forall GenericPick._default.SeqPick2$U: Ty, $Heap: Heap, s#0: Seq Box :: 
  { GenericPick.__default.SeqPick2#requires(GenericPick._default.SeqPick2$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TSeq(GenericPick._default.SeqPick2$U))
     ==> GenericPick.__default.SeqPick2#requires(GenericPick._default.SeqPick2$U, s#0)
       == (exists x#9: Box :: 
        { Seq#Contains(s#0, x#9) } 
        $IsBox(x#9, GenericPick._default.SeqPick2$U) && Seq#Contains(s#0, x#9)));

function $let#41_x(GenericPick._default.SeqPick2$U: Ty, s: Seq Box) : Box;

function $let#41$canCall(GenericPick._default.SeqPick2$U: Ty, s: Seq Box) : bool;

axiom (forall GenericPick._default.SeqPick2$U: Ty, s: Seq Box :: 
  { $let#41_x(GenericPick._default.SeqPick2$U, s) } 
  $let#41$canCall(GenericPick._default.SeqPick2$U, s)
     ==> Seq#Contains(s, $let#41_x(GenericPick._default.SeqPick2$U, s)));

// definition axiom for GenericPick.__default.SeqPick2 (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick2$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick2(GenericPick._default.SeqPick2$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick2#canCall(GenericPick._default.SeqPick2$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick2$U))
           && (exists x#9: Box :: 
            { Seq#Contains(s#0, x#9) } 
            $IsBox(x#9, GenericPick._default.SeqPick2$U) && Seq#Contains(s#0, x#9)))
       ==> $let#41$canCall(GenericPick._default.SeqPick2$U, s#0)
         && GenericPick.__default.SeqPick2(GenericPick._default.SeqPick2$U, s#0)
           == (var x#10 := $let#41_x(GenericPick._default.SeqPick2$U, s#0); x#10));

// definition axiom for GenericPick.__default.SeqPick2 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick2$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    {:weight 3} { GenericPick.__default.SeqPick2(GenericPick._default.SeqPick2$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick2#canCall(GenericPick._default.SeqPick2$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick2$U))
           && (exists x#11: Box :: 
            { Seq#Contains(s#0, x#11) } 
            $IsBox(x#11, GenericPick._default.SeqPick2$U) && Seq#Contains(s#0, x#11)))
       ==> $let#41$canCall(GenericPick._default.SeqPick2$U, Lit(s#0))
         && GenericPick.__default.SeqPick2(GenericPick._default.SeqPick2$U, Lit(s#0))
           == (var x#12 := $let#41_x(GenericPick._default.SeqPick2$U, Lit(s#0)); x#12));

// function declaration for GenericPick._default.SeqPick3
function GenericPick.__default.SeqPick3(GenericPick._default.SeqPick3$U: Ty, s#0: Seq Box) : Box;

function GenericPick.__default.SeqPick3#canCall(GenericPick._default.SeqPick3$U: Ty, s#0: Seq Box) : bool;

// consequence axiom for GenericPick.__default.SeqPick3
axiom true
   ==> (forall GenericPick._default.SeqPick3$U: Ty, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick3(GenericPick._default.SeqPick3$U, s#0) } 
    GenericPick.__default.SeqPick3#canCall(GenericPick._default.SeqPick3$U, s#0)
         || ($Is(s#0, TSeq(GenericPick._default.SeqPick3$U))
           && (exists i#4: int :: {:nowarn} LitInt(0) <= i#4 && i#4 < Seq#Length(s#0)))
       ==> $IsBox(GenericPick.__default.SeqPick3(GenericPick._default.SeqPick3$U, s#0), 
        GenericPick._default.SeqPick3$U));

function GenericPick.__default.SeqPick3#requires(Ty, Seq Box) : bool;

// #requires axiom for GenericPick.__default.SeqPick3
axiom (forall GenericPick._default.SeqPick3$U: Ty, $Heap: Heap, s#0: Seq Box :: 
  { GenericPick.__default.SeqPick3#requires(GenericPick._default.SeqPick3$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TSeq(GenericPick._default.SeqPick3$U))
     ==> GenericPick.__default.SeqPick3#requires(GenericPick._default.SeqPick3$U, s#0)
       == (exists i#5: int :: {:nowarn} LitInt(0) <= i#5 && i#5 < Seq#Length(s#0)));

function $let#44_x(GenericPick._default.SeqPick3$U: Ty, s: Seq Box) : Box;

function $let#44$canCall(GenericPick._default.SeqPick3$U: Ty, s: Seq Box) : bool;

axiom (forall GenericPick._default.SeqPick3$U: Ty, s: Seq Box :: 
  { $let#44_x(GenericPick._default.SeqPick3$U, s) } 
  $let#44$canCall(GenericPick._default.SeqPick3$U, s)
     ==> Seq#Contains(s, $let#44_x(GenericPick._default.SeqPick3$U, s)));

// definition axiom for GenericPick.__default.SeqPick3 (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick3$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick3(GenericPick._default.SeqPick3$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick3#canCall(GenericPick._default.SeqPick3$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick3$U))
           && (exists i#5: int :: {:nowarn} LitInt(0) <= i#5 && i#5 < Seq#Length(s#0)))
       ==> $let#44$canCall(GenericPick._default.SeqPick3$U, s#0)
         && GenericPick.__default.SeqPick3(GenericPick._default.SeqPick3$U, s#0)
           == (var x#4 := $let#44_x(GenericPick._default.SeqPick3$U, s#0); x#4));

// definition axiom for GenericPick.__default.SeqPick3 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick3$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    {:weight 3} { GenericPick.__default.SeqPick3(GenericPick._default.SeqPick3$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick3#canCall(GenericPick._default.SeqPick3$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick3$U))
           && (exists i#6: int :: {:nowarn} LitInt(0) <= i#6 && i#6 < Seq#Length(Lit(s#0))))
       ==> $let#44$canCall(GenericPick._default.SeqPick3$U, Lit(s#0))
         && GenericPick.__default.SeqPick3(GenericPick._default.SeqPick3$U, Lit(s#0))
           == (var x#5 := $let#44_x(GenericPick._default.SeqPick3$U, Lit(s#0)); x#5));

// function declaration for GenericPick._default.SeqPick4
function GenericPick.__default.SeqPick4(GenericPick._default.SeqPick4$U: Ty, s#0: Seq Box) : Box;

function GenericPick.__default.SeqPick4#canCall(GenericPick._default.SeqPick4$U: Ty, s#0: Seq Box) : bool;

// consequence axiom for GenericPick.__default.SeqPick4
axiom true
   ==> (forall GenericPick._default.SeqPick4$U: Ty, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick4(GenericPick._default.SeqPick4$U, s#0) } 
    GenericPick.__default.SeqPick4#canCall(GenericPick._default.SeqPick4$U, s#0)
         || ($Is(s#0, TSeq(GenericPick._default.SeqPick4$U))
           && (exists i#8: int :: {:nowarn} LitInt(0) <= i#8 && i#8 < Seq#Length(s#0)))
       ==> $IsBox(GenericPick.__default.SeqPick4(GenericPick._default.SeqPick4$U, s#0), 
        GenericPick._default.SeqPick4$U));

function GenericPick.__default.SeqPick4#requires(Ty, Seq Box) : bool;

// #requires axiom for GenericPick.__default.SeqPick4
axiom (forall GenericPick._default.SeqPick4$U: Ty, $Heap: Heap, s#0: Seq Box :: 
  { GenericPick.__default.SeqPick4#requires(GenericPick._default.SeqPick4$U, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(s#0, TSeq(GenericPick._default.SeqPick4$U))
     ==> GenericPick.__default.SeqPick4#requires(GenericPick._default.SeqPick4$U, s#0)
       == (exists i#9: int :: {:nowarn} LitInt(0) <= i#9 && i#9 < Seq#Length(s#0)));

function $let#47_i(GenericPick._default.SeqPick4$U: Ty, s: Seq Box) : int;

function $let#47$canCall(GenericPick._default.SeqPick4$U: Ty, s: Seq Box) : bool;

axiom (forall GenericPick._default.SeqPick4$U: Ty, s: Seq Box :: 
  { $let#47_i(GenericPick._default.SeqPick4$U, s) } 
  $let#47$canCall(GenericPick._default.SeqPick4$U, s)
     ==> LitInt(0) <= $let#47_i(GenericPick._default.SeqPick4$U, s)
       && $let#47_i(GenericPick._default.SeqPick4$U, s) < Seq#Length(s));

// definition axiom for GenericPick.__default.SeqPick4 (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick4$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    { GenericPick.__default.SeqPick4(GenericPick._default.SeqPick4$U, s#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick4#canCall(GenericPick._default.SeqPick4$U, s#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick4$U))
           && (exists i#9: int :: {:nowarn} LitInt(0) <= i#9 && i#9 < Seq#Length(s#0)))
       ==> $let#47$canCall(GenericPick._default.SeqPick4$U, s#0)
         && GenericPick.__default.SeqPick4(GenericPick._default.SeqPick4$U, s#0)
           == (var i#10 := $let#47_i(GenericPick._default.SeqPick4$U, s#0); 
            Seq#Index(s#0, i#10)));

// definition axiom for GenericPick.__default.SeqPick4 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.SeqPick4$U: Ty, $Heap: Heap, s#0: Seq Box :: 
    {:weight 3} { GenericPick.__default.SeqPick4(GenericPick._default.SeqPick4$U, Lit(s#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.SeqPick4#canCall(GenericPick._default.SeqPick4$U, Lit(s#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(s#0, TSeq(GenericPick._default.SeqPick4$U))
           && (exists i#11: int :: {:nowarn} LitInt(0) <= i#11 && i#11 < Seq#Length(Lit(s#0))))
       ==> $let#47$canCall(GenericPick._default.SeqPick4$U, Lit(s#0))
         && GenericPick.__default.SeqPick4(GenericPick._default.SeqPick4$U, Lit(s#0))
           == (var i#12 := $let#47_i(GenericPick._default.SeqPick4$U, Lit(s#0)); 
            Seq#Index(Lit(s#0), i#12)));

// function declaration for GenericPick._default.MapPick0
function GenericPick.__default.MapPick0(GenericPick._default.MapPick0$U: Ty, 
    GenericPick._default.MapPick0$V: Ty, 
    m#0: Map Box Box)
   : Box;

function GenericPick.__default.MapPick0#canCall(GenericPick._default.MapPick0$U: Ty, 
    GenericPick._default.MapPick0$V: Ty, 
    m#0: Map Box Box)
   : bool;

// consequence axiom for GenericPick.__default.MapPick0
axiom true
   ==> (forall GenericPick._default.MapPick0$U: Ty, 
      GenericPick._default.MapPick0$V: Ty, 
      m#0: Map Box Box :: 
    { GenericPick.__default.MapPick0(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0) } 
    GenericPick.__default.MapPick0#canCall(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0)
         || ($Is(m#0, TMap(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V))
           && !Map#Equal(m#0, Map#Empty(): Map Box Box))
       ==> $IsBox(GenericPick.__default.MapPick0(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0), 
        GenericPick._default.MapPick0$U));

function GenericPick.__default.MapPick0#requires(Ty, Ty, Map Box Box) : bool;

// #requires axiom for GenericPick.__default.MapPick0
axiom (forall GenericPick._default.MapPick0$U: Ty, 
    GenericPick._default.MapPick0$V: Ty, 
    $Heap: Heap, 
    m#0: Map Box Box :: 
  { GenericPick.__default.MapPick0#requires(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(m#0, TMap(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V))
     ==> GenericPick.__default.MapPick0#requires(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0)
       == !Map#Equal(m#0, Map#Empty(): Map Box Box));

function $let#50_x(GenericPick._default.MapPick0$U: Ty, 
    GenericPick._default.MapPick0$V: Ty, 
    m: Map Box Box)
   : Box;

function $let#50$canCall(GenericPick._default.MapPick0$U: Ty, 
    GenericPick._default.MapPick0$V: Ty, 
    m: Map Box Box)
   : bool;

axiom (forall GenericPick._default.MapPick0$U: Ty, 
    GenericPick._default.MapPick0$V: Ty, 
    m: Map Box Box :: 
  { $let#50_x(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m) } 
  $let#50$canCall(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m)
     ==> Map#Domain(m)[$let#50_x(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m)]);

// definition axiom for GenericPick.__default.MapPick0 (revealed)
axiom true
   ==> (forall GenericPick._default.MapPick0$U: Ty, 
      GenericPick._default.MapPick0$V: Ty, 
      $Heap: Heap, 
      m#0: Map Box Box :: 
    { GenericPick.__default.MapPick0(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.MapPick0#canCall(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(m#0, TMap(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V))
           && !Map#Equal(m#0, Map#Empty(): Map Box Box))
       ==> $let#50$canCall(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0)
         && GenericPick.__default.MapPick0(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0)
           == (var x#4 := $let#50_x(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, m#0); 
            x#4));

// definition axiom for GenericPick.__default.MapPick0 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.MapPick0$U: Ty, 
      GenericPick._default.MapPick0$V: Ty, 
      $Heap: Heap, 
      m#0: Map Box Box :: 
    {:weight 3} { GenericPick.__default.MapPick0(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, Lit(m#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.MapPick0#canCall(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, Lit(m#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(m#0, TMap(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V))
           && !Map#Equal(m#0, Map#Empty(): Map Box Box))
       ==> $let#50$canCall(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, Lit(m#0))
         && GenericPick.__default.MapPick0(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, Lit(m#0))
           == (var x#5 := $let#50_x(GenericPick._default.MapPick0$U, GenericPick._default.MapPick0$V, Lit(m#0)); 
            x#5));

// function declaration for GenericPick._default.MapPick1
function GenericPick.__default.MapPick1(GenericPick._default.MapPick1$U: Ty, 
    GenericPick._default.MapPick1$V: Ty, 
    m#0: Map Box Box)
   : Box;

function GenericPick.__default.MapPick1#canCall(GenericPick._default.MapPick1$U: Ty, 
    GenericPick._default.MapPick1$V: Ty, 
    m#0: Map Box Box)
   : bool;

// consequence axiom for GenericPick.__default.MapPick1
axiom true
   ==> (forall GenericPick._default.MapPick1$U: Ty, 
      GenericPick._default.MapPick1$V: Ty, 
      m#0: Map Box Box :: 
    { GenericPick.__default.MapPick1(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0) } 
    GenericPick.__default.MapPick1#canCall(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0)
         || ($Is(m#0, TMap(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V))
           && Map#Card(m#0) != 0)
       ==> $IsBox(GenericPick.__default.MapPick1(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0), 
        GenericPick._default.MapPick1$U));

function GenericPick.__default.MapPick1#requires(Ty, Ty, Map Box Box) : bool;

// #requires axiom for GenericPick.__default.MapPick1
axiom (forall GenericPick._default.MapPick1$U: Ty, 
    GenericPick._default.MapPick1$V: Ty, 
    $Heap: Heap, 
    m#0: Map Box Box :: 
  { GenericPick.__default.MapPick1#requires(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(m#0, TMap(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V))
     ==> GenericPick.__default.MapPick1#requires(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0)
       == (Map#Card(m#0) != 0));

function $let#53_x(GenericPick._default.MapPick1$U: Ty, 
    GenericPick._default.MapPick1$V: Ty, 
    m: Map Box Box)
   : Box;

function $let#53$canCall(GenericPick._default.MapPick1$U: Ty, 
    GenericPick._default.MapPick1$V: Ty, 
    m: Map Box Box)
   : bool;

axiom (forall GenericPick._default.MapPick1$U: Ty, 
    GenericPick._default.MapPick1$V: Ty, 
    m: Map Box Box :: 
  { $let#53_x(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m) } 
  $let#53$canCall(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m)
     ==> Map#Domain(m)[$let#53_x(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m)]);

// definition axiom for GenericPick.__default.MapPick1 (revealed)
axiom true
   ==> (forall GenericPick._default.MapPick1$U: Ty, 
      GenericPick._default.MapPick1$V: Ty, 
      $Heap: Heap, 
      m#0: Map Box Box :: 
    { GenericPick.__default.MapPick1(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.MapPick1#canCall(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(m#0, TMap(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V))
           && Map#Card(m#0) != 0)
       ==> $let#53$canCall(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0)
         && GenericPick.__default.MapPick1(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0)
           == (var x#4 := $let#53_x(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, m#0); 
            x#4));

// definition axiom for GenericPick.__default.MapPick1 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.MapPick1$U: Ty, 
      GenericPick._default.MapPick1$V: Ty, 
      $Heap: Heap, 
      m#0: Map Box Box :: 
    {:weight 3} { GenericPick.__default.MapPick1(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, Lit(m#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.MapPick1#canCall(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, Lit(m#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(m#0, TMap(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V))
           && Map#Card(Lit(m#0)) != 0)
       ==> $let#53$canCall(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, Lit(m#0))
         && GenericPick.__default.MapPick1(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, Lit(m#0))
           == (var x#5 := $let#53_x(GenericPick._default.MapPick1$U, GenericPick._default.MapPick1$V, Lit(m#0)); 
            x#5));

// function declaration for GenericPick._default.MapPick2
function GenericPick.__default.MapPick2(GenericPick._default.MapPick2$U: Ty, 
    GenericPick._default.MapPick2$V: Ty, 
    m#0: Map Box Box)
   : Box;

function GenericPick.__default.MapPick2#canCall(GenericPick._default.MapPick2$U: Ty, 
    GenericPick._default.MapPick2$V: Ty, 
    m#0: Map Box Box)
   : bool;

// consequence axiom for GenericPick.__default.MapPick2
axiom true
   ==> (forall GenericPick._default.MapPick2$U: Ty, 
      GenericPick._default.MapPick2$V: Ty, 
      m#0: Map Box Box :: 
    { GenericPick.__default.MapPick2(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0) } 
    GenericPick.__default.MapPick2#canCall(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0)
         || ($Is(m#0, TMap(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V))
           && (exists x#8: Box :: 
            { Map#Domain(m#0)[x#8] } 
            $IsBox(x#8, GenericPick._default.MapPick2$U) && Map#Domain(m#0)[x#8]))
       ==> $IsBox(GenericPick.__default.MapPick2(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0), 
        GenericPick._default.MapPick2$U));

function GenericPick.__default.MapPick2#requires(Ty, Ty, Map Box Box) : bool;

// #requires axiom for GenericPick.__default.MapPick2
axiom (forall GenericPick._default.MapPick2$U: Ty, 
    GenericPick._default.MapPick2$V: Ty, 
    $Heap: Heap, 
    m#0: Map Box Box :: 
  { GenericPick.__default.MapPick2#requires(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(m#0, TMap(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V))
     ==> GenericPick.__default.MapPick2#requires(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0)
       == (exists x#9: Box :: 
        { Map#Domain(m#0)[x#9] } 
        $IsBox(x#9, GenericPick._default.MapPick2$U) && Map#Domain(m#0)[x#9]));

function $let#56_x(GenericPick._default.MapPick2$U: Ty, 
    GenericPick._default.MapPick2$V: Ty, 
    m: Map Box Box)
   : Box;

function $let#56$canCall(GenericPick._default.MapPick2$U: Ty, 
    GenericPick._default.MapPick2$V: Ty, 
    m: Map Box Box)
   : bool;

axiom (forall GenericPick._default.MapPick2$U: Ty, 
    GenericPick._default.MapPick2$V: Ty, 
    m: Map Box Box :: 
  { $let#56_x(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m) } 
  $let#56$canCall(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m)
     ==> Map#Domain(m)[$let#56_x(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m)]);

// definition axiom for GenericPick.__default.MapPick2 (revealed)
axiom true
   ==> (forall GenericPick._default.MapPick2$U: Ty, 
      GenericPick._default.MapPick2$V: Ty, 
      $Heap: Heap, 
      m#0: Map Box Box :: 
    { GenericPick.__default.MapPick2(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0), $IsGoodHeap($Heap) } 
    GenericPick.__default.MapPick2#canCall(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0)
         || (
          $IsGoodHeap($Heap)
           && $Is(m#0, TMap(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V))
           && (exists x#9: Box :: 
            { Map#Domain(m#0)[x#9] } 
            $IsBox(x#9, GenericPick._default.MapPick2$U) && Map#Domain(m#0)[x#9]))
       ==> $let#56$canCall(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0)
         && GenericPick.__default.MapPick2(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0)
           == (var x#10 := $let#56_x(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, m#0); 
            x#10));

// definition axiom for GenericPick.__default.MapPick2 for all literals (revealed)
axiom true
   ==> (forall GenericPick._default.MapPick2$U: Ty, 
      GenericPick._default.MapPick2$V: Ty, 
      $Heap: Heap, 
      m#0: Map Box Box :: 
    {:weight 3} { GenericPick.__default.MapPick2(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, Lit(m#0)), $IsGoodHeap($Heap) } 
    GenericPick.__default.MapPick2#canCall(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, Lit(m#0))
         || (
          $IsGoodHeap($Heap)
           && $Is(m#0, TMap(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V))
           && (exists x#11: Box :: 
            { Map#Domain(m#0)[x#11] } 
            $IsBox(x#11, GenericPick._default.MapPick2$U) && Map#Domain(m#0)[x#11]))
       ==> $let#56$canCall(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, Lit(m#0))
         && GenericPick.__default.MapPick2(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, Lit(m#0))
           == (var x#12 := $let#56_x(GenericPick._default.MapPick2$U, GenericPick._default.MapPick2$V, Lit(m#0)); 
            x#12));

// Constructor function declaration
function #ListLibrary.List.Nil() : DatatypeType;

const unique ##ListLibrary.List.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#ListLibrary.List.Nil()) == ##ListLibrary.List.Nil;

function ListLibrary.List.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ListLibrary.List.Nil_q(d) } 
  ListLibrary.List.Nil_q(d) <==> DatatypeCtorId(d) == ##ListLibrary.List.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ListLibrary.List.Nil_q(d) } 
  ListLibrary.List.Nil_q(d) ==> d == #ListLibrary.List.Nil());

function Tclass.ListLibrary.List(Ty) : Ty;

const unique Tagclass.ListLibrary.List: TyTag;

// Tclass.ListLibrary.List Tag
axiom (forall ListLibrary.List$T: Ty :: 
  { Tclass.ListLibrary.List(ListLibrary.List$T) } 
  Tag(Tclass.ListLibrary.List(ListLibrary.List$T)) == Tagclass.ListLibrary.List
     && TagFamily(Tclass.ListLibrary.List(ListLibrary.List$T)) == tytagFamily$List);

// Tclass.ListLibrary.List injectivity 0
axiom (forall ListLibrary.List$T: Ty :: 
  { Tclass.ListLibrary.List(ListLibrary.List$T) } 
  Tclass.ListLibrary.List_0(Tclass.ListLibrary.List(ListLibrary.List$T))
     == ListLibrary.List$T);

function Tclass.ListLibrary.List_0(Ty) : Ty;

// Box/unbox axiom for Tclass.ListLibrary.List
axiom (forall ListLibrary.List$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.ListLibrary.List(ListLibrary.List$T)) } 
  $IsBox(bx, Tclass.ListLibrary.List(ListLibrary.List$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.ListLibrary.List(ListLibrary.List$T)));

// Constructor $Is
axiom (forall ListLibrary.List$T: Ty :: 
  { $Is(#ListLibrary.List.Nil(), Tclass.ListLibrary.List(ListLibrary.List$T)) } 
  $Is(#ListLibrary.List.Nil(), Tclass.ListLibrary.List(ListLibrary.List$T)));

// Constructor $IsAlloc
axiom (forall ListLibrary.List$T: Ty, $h: Heap :: 
  { $IsAlloc(#ListLibrary.List.Nil(), Tclass.ListLibrary.List(ListLibrary.List$T), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#ListLibrary.List.Nil(), Tclass.ListLibrary.List(ListLibrary.List$T), $h));

// Constructor literal
axiom #ListLibrary.List.Nil() == Lit(#ListLibrary.List.Nil());

// Constructor function declaration
function #ListLibrary.List.Cons(Box, DatatypeType) : DatatypeType;

const unique ##ListLibrary.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: DatatypeType :: 
  { #ListLibrary.List.Cons(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#ListLibrary.List.Cons(a#5#0#0, a#5#1#0))
     == ##ListLibrary.List.Cons);

function ListLibrary.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ListLibrary.List.Cons_q(d) } 
  ListLibrary.List.Cons_q(d) <==> DatatypeCtorId(d) == ##ListLibrary.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ListLibrary.List.Cons_q(d) } 
  ListLibrary.List.Cons_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: DatatypeType :: 
      d == #ListLibrary.List.Cons(a#6#0#0, a#6#1#0)));

// Constructor $Is
axiom (forall ListLibrary.List$T: Ty, a#7#0#0: Box, a#7#1#0: DatatypeType :: 
  { $Is(#ListLibrary.List.Cons(a#7#0#0, a#7#1#0), 
      Tclass.ListLibrary.List(ListLibrary.List$T)) } 
  $Is(#ListLibrary.List.Cons(a#7#0#0, a#7#1#0), 
      Tclass.ListLibrary.List(ListLibrary.List$T))
     <==> $IsBox(a#7#0#0, ListLibrary.List$T)
       && $Is(a#7#1#0, Tclass.ListLibrary.List(ListLibrary.List$T)));

// Constructor $IsAlloc
axiom (forall ListLibrary.List$T: Ty, a#8#0#0: Box, a#8#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#ListLibrary.List.Cons(a#8#0#0, a#8#1#0), 
      Tclass.ListLibrary.List(ListLibrary.List$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ListLibrary.List.Cons(a#8#0#0, a#8#1#0), 
        Tclass.ListLibrary.List(ListLibrary.List$T), 
        $h)
       <==> $IsAllocBox(a#8#0#0, ListLibrary.List$T, $h)
         && $IsAlloc(a#8#1#0, Tclass.ListLibrary.List(ListLibrary.List$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ListLibrary.List$T: Ty, $h: Heap :: 
  { $IsAllocBox(ListLibrary.List._h3(d), ListLibrary.List$T, $h) } 
  $IsGoodHeap($h)
       && 
      ListLibrary.List.Cons_q(d)
       && $IsAlloc(d, Tclass.ListLibrary.List(ListLibrary.List$T), $h)
     ==> $IsAllocBox(ListLibrary.List._h3(d), ListLibrary.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ListLibrary.List$T: Ty, $h: Heap :: 
  { $IsAlloc(ListLibrary.List._h4(d), Tclass.ListLibrary.List(ListLibrary.List$T), $h) } 
  $IsGoodHeap($h)
       && 
      ListLibrary.List.Cons_q(d)
       && $IsAlloc(d, Tclass.ListLibrary.List(ListLibrary.List$T), $h)
     ==> $IsAlloc(ListLibrary.List._h4(d), Tclass.ListLibrary.List(ListLibrary.List$T), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType :: 
  { #ListLibrary.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #ListLibrary.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#ListLibrary.List.Cons(a#9#0#0, a#9#1#0)));

function ListLibrary.List._h3(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType :: 
  { #ListLibrary.List.Cons(a#10#0#0, a#10#1#0) } 
  ListLibrary.List._h3(#ListLibrary.List.Cons(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType :: 
  { #ListLibrary.List.Cons(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#ListLibrary.List.Cons(a#11#0#0, a#11#1#0)));

function ListLibrary.List._h4(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType :: 
  { #ListLibrary.List.Cons(a#12#0#0, a#12#1#0) } 
  ListLibrary.List._h4(#ListLibrary.List.Cons(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: DatatypeType :: 
  { #ListLibrary.List.Cons(a#13#0#0, a#13#1#0) } 
  DtRank(a#13#1#0) < DtRank(#ListLibrary.List.Cons(a#13#0#0, a#13#1#0)));

// Depth-one case-split function
function $IsA#ListLibrary.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ListLibrary.List(d) } 
  $IsA#ListLibrary.List(d)
     ==> ListLibrary.List.Nil_q(d) || ListLibrary.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall ListLibrary.List$T: Ty, d: DatatypeType :: 
  { ListLibrary.List.Cons_q(d), $Is(d, Tclass.ListLibrary.List(ListLibrary.List$T)) } 
    { ListLibrary.List.Nil_q(d), $Is(d, Tclass.ListLibrary.List(ListLibrary.List$T)) } 
  $Is(d, Tclass.ListLibrary.List(ListLibrary.List$T))
     ==> ListLibrary.List.Nil_q(d) || ListLibrary.List.Cons_q(d));

// Datatype extensional equality declaration
function ListLibrary.List#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ListLibrary.List.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ListLibrary.List#Equal(a, b), ListLibrary.List.Nil_q(a) } 
    { ListLibrary.List#Equal(a, b), ListLibrary.List.Nil_q(b) } 
  ListLibrary.List.Nil_q(a) && ListLibrary.List.Nil_q(b)
     ==> (ListLibrary.List#Equal(a, b) <==> true));

// Datatype extensional equality definition: #ListLibrary.List.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ListLibrary.List#Equal(a, b), ListLibrary.List.Cons_q(a) } 
    { ListLibrary.List#Equal(a, b), ListLibrary.List.Cons_q(b) } 
  ListLibrary.List.Cons_q(a) && ListLibrary.List.Cons_q(b)
     ==> (ListLibrary.List#Equal(a, b)
       <==> ListLibrary.List._h3(a) == ListLibrary.List._h3(b)
         && ListLibrary.List#Equal(ListLibrary.List._h4(a), ListLibrary.List._h4(b))));

// Datatype extensionality axiom: ListLibrary.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ListLibrary.List#Equal(a, b) } 
  ListLibrary.List#Equal(a, b) <==> a == b);

const unique class.ListLibrary.List: ClassName;

const unique class.ListLibrary.__default: ClassName;

function Tclass.ListLibrary.__default() : Ty;

const unique Tagclass.ListLibrary.__default: TyTag;

// Tclass.ListLibrary.__default Tag
axiom Tag(Tclass.ListLibrary.__default()) == Tagclass.ListLibrary.__default
   && TagFamily(Tclass.ListLibrary.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ListLibrary.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ListLibrary.__default()) } 
  $IsBox(bx, Tclass.ListLibrary.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ListLibrary.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ListLibrary.__default()) } 
  $Is($o, Tclass.ListLibrary.__default())
     <==> $o == null || dtype($o) == Tclass.ListLibrary.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ListLibrary.__default(), $h) } 
  $IsAlloc($o, Tclass.ListLibrary.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const #$_default: Ty;

const unique class.ListLibraryIndirect.__default: ClassName;

function Tclass.ListLibraryIndirect.__default() : Ty;

const unique Tagclass.ListLibraryIndirect.__default: TyTag;

// Tclass.ListLibraryIndirect.__default Tag
axiom Tag(Tclass.ListLibraryIndirect.__default())
     == Tagclass.ListLibraryIndirect.__default
   && TagFamily(Tclass.ListLibraryIndirect.__default()) == tytagFamily$_default;

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ListLibraryIndirect.__default()) } 
  $Is($o, Tclass.ListLibraryIndirect.__default())
     <==> $o == null || dtype($o) == Tclass.ListLibraryIndirect.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ListLibraryIndirect.__default(), $h) } 
  $IsAlloc($o, Tclass.ListLibraryIndirect.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.DatatypeTestZ.__default: ClassName;

function Tclass.DatatypeTestZ.__default() : Ty;

const unique Tagclass.DatatypeTestZ.__default: TyTag;

// Tclass.DatatypeTestZ.__default Tag
axiom Tag(Tclass.DatatypeTestZ.__default()) == Tagclass.DatatypeTestZ.__default
   && TagFamily(Tclass.DatatypeTestZ.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.DatatypeTestZ.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.DatatypeTestZ.__default()) } 
  $IsBox(bx, Tclass.DatatypeTestZ.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.DatatypeTestZ.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.DatatypeTestZ.__default()) } 
  $Is($o, Tclass.DatatypeTestZ.__default())
     <==> $o == null || dtype($o) == Tclass.DatatypeTestZ.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.DatatypeTestZ.__default(), $h) } 
  $IsAlloc($o, Tclass.DatatypeTestZ.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass.ConstantFieldReceiverNonNull.Six() : Ty;

const unique Tagclass.ConstantFieldReceiverNonNull.Six: TyTag;

// Tclass.ConstantFieldReceiverNonNull.Six Tag
axiom Tag(Tclass.ConstantFieldReceiverNonNull.Six())
     == Tagclass.ConstantFieldReceiverNonNull.Six
   && TagFamily(Tclass.ConstantFieldReceiverNonNull.Six()) == tytagFamily$Six;

// Box/unbox axiom for Tclass.ConstantFieldReceiverNonNull.Six
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Six()) } 
  $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Six())
     ==> $Box($Unbox(bx): int) == bx
       && $Is($Unbox(bx): int, Tclass.ConstantFieldReceiverNonNull.Six()));

// ConstantFieldReceiverNonNull.Six: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass.ConstantFieldReceiverNonNull.Six()) } 
  $Is(x#0, Tclass.ConstantFieldReceiverNonNull.Six()) <==> LitInt(6) <= x#0);

// ConstantFieldReceiverNonNull.Six: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass.ConstantFieldReceiverNonNull.Six(), $h) } 
  $IsAlloc(x#0, Tclass.ConstantFieldReceiverNonNull.Six(), $h));

const unique class.ConstantFieldReceiverNonNull.Six: ClassName;

const unique class.ConstantFieldReceiverNonNull.Trait?: ClassName;

function Tclass.ConstantFieldReceiverNonNull.Trait?() : Ty;

const unique Tagclass.ConstantFieldReceiverNonNull.Trait?: TyTag;

// Tclass.ConstantFieldReceiverNonNull.Trait? Tag
axiom Tag(Tclass.ConstantFieldReceiverNonNull.Trait?())
     == Tagclass.ConstantFieldReceiverNonNull.Trait?
   && TagFamily(Tclass.ConstantFieldReceiverNonNull.Trait?()) == tytagFamily$Trait;

// Box/unbox axiom for Tclass.ConstantFieldReceiverNonNull.Trait?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Trait?()) } 
  $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Trait?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ConstantFieldReceiverNonNull.Trait?()));

// Trait: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ConstantFieldReceiverNonNull.Trait?()) } 
  $Is($o, Tclass.ConstantFieldReceiverNonNull.Trait?())
     <==> $o == null || implements$ConstantFieldReceiverNonNull.Trait(dtype($o)));

// Trait: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.Trait?(), $h) } 
  $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.Trait?(), $h)
     <==> $o == null || read($h, $o, alloc));

function implements$ConstantFieldReceiverNonNull.Trait(Ty) : bool;

function ConstantFieldReceiverNonNull.Trait.x0(this: ref) : int;

// Trait.x0: Type axiom
axiom (forall $o: ref :: 
  { ConstantFieldReceiverNonNull.Trait.x0($o) } 
  $Is(ConstantFieldReceiverNonNull.Trait.x0($o), 
    Tclass.ConstantFieldReceiverNonNull.Six()));

// Trait.x0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ConstantFieldReceiverNonNull.Trait.x0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(ConstantFieldReceiverNonNull.Trait.x0($o), 
      Tclass.ConstantFieldReceiverNonNull.Six(), 
      $h));

function {:inline} ConstantFieldReceiverNonNull.Trait.x1(this: ref) : int
{
  LitInt(7)
}

// Trait.x1: Type axiom
axiom (forall $o: ref :: 
  { ConstantFieldReceiverNonNull.Trait.x1($o) } 
  $Is(ConstantFieldReceiverNonNull.Trait.x1($o), 
    Tclass.ConstantFieldReceiverNonNull.Six()));

// Trait.x1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ConstantFieldReceiverNonNull.Trait.x1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(ConstantFieldReceiverNonNull.Trait.x1($o), 
      Tclass.ConstantFieldReceiverNonNull.Six(), 
      $h));

function {:inline} ConstantFieldReceiverNonNull.Trait.y() : int
{
  LitInt(7)
}

// Trait.y: Type axiom
axiom $Is(ConstantFieldReceiverNonNull.Trait.y(), 
  Tclass.ConstantFieldReceiverNonNull.Six());

// Trait.y: Allocation axiom
axiom (forall $h: Heap :: 
  { $IsAlloc(ConstantFieldReceiverNonNull.Trait.y(), 
      Tclass.ConstantFieldReceiverNonNull.Six(), 
      $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(ConstantFieldReceiverNonNull.Trait.y(), 
      Tclass.ConstantFieldReceiverNonNull.Six(), 
      $h));

function Tclass.ConstantFieldReceiverNonNull.Trait() : Ty;

const unique Tagclass.ConstantFieldReceiverNonNull.Trait: TyTag;

// Tclass.ConstantFieldReceiverNonNull.Trait Tag
axiom Tag(Tclass.ConstantFieldReceiverNonNull.Trait())
     == Tagclass.ConstantFieldReceiverNonNull.Trait
   && TagFamily(Tclass.ConstantFieldReceiverNonNull.Trait()) == tytagFamily$Trait;

// Box/unbox axiom for Tclass.ConstantFieldReceiverNonNull.Trait
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Trait()) } 
  $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Trait())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ConstantFieldReceiverNonNull.Trait()));

// ConstantFieldReceiverNonNull.Trait: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ConstantFieldReceiverNonNull.Trait()) } 
  $Is(c#0, Tclass.ConstantFieldReceiverNonNull.Trait())
     <==> $Is(c#0, Tclass.ConstantFieldReceiverNonNull.Trait?()) && c#0 != null);

// ConstantFieldReceiverNonNull.Trait: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.Trait(), $h) } 
  $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.Trait(), $h)
     <==> $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.Trait?(), $h));

const unique class.ConstantFieldReceiverNonNull.Class?: ClassName;

function Tclass.ConstantFieldReceiverNonNull.Class?() : Ty;

const unique Tagclass.ConstantFieldReceiverNonNull.Class?: TyTag;

// Tclass.ConstantFieldReceiverNonNull.Class? Tag
axiom Tag(Tclass.ConstantFieldReceiverNonNull.Class?())
     == Tagclass.ConstantFieldReceiverNonNull.Class?
   && TagFamily(Tclass.ConstantFieldReceiverNonNull.Class?()) == tytagFamily$Class;

// Box/unbox axiom for Tclass.ConstantFieldReceiverNonNull.Class?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Class?()) } 
  $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Class?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ConstantFieldReceiverNonNull.Class?()));

// Class: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ConstantFieldReceiverNonNull.Class?()) } 
  $Is($o, Tclass.ConstantFieldReceiverNonNull.Class?())
     <==> $o == null || dtype($o) == Tclass.ConstantFieldReceiverNonNull.Class?());

// Class: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.Class?(), $h) } 
  $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.Class?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom implements$ConstantFieldReceiverNonNull.Trait(Tclass.ConstantFieldReceiverNonNull.Class?());

function Tclass.ConstantFieldReceiverNonNull.Class() : Ty;

const unique Tagclass.ConstantFieldReceiverNonNull.Class: TyTag;

// Tclass.ConstantFieldReceiverNonNull.Class Tag
axiom Tag(Tclass.ConstantFieldReceiverNonNull.Class())
     == Tagclass.ConstantFieldReceiverNonNull.Class
   && TagFamily(Tclass.ConstantFieldReceiverNonNull.Class()) == tytagFamily$Class;

// Box/unbox axiom for Tclass.ConstantFieldReceiverNonNull.Class
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Class()) } 
  $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.Class())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ConstantFieldReceiverNonNull.Class()));

// ConstantFieldReceiverNonNull.Class: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ConstantFieldReceiverNonNull.Class()) } 
  $Is(c#0, Tclass.ConstantFieldReceiverNonNull.Class())
     <==> $Is(c#0, Tclass.ConstantFieldReceiverNonNull.Class?()) && c#0 != null);

// ConstantFieldReceiverNonNull.Class: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.Class(), $h) } 
  $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.Class(), $h)
     <==> $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.Class?(), $h));

const unique class.ConstantFieldReceiverNonNull.AnotherClass?: ClassName;

function Tclass.ConstantFieldReceiverNonNull.AnotherClass?() : Ty;

const unique Tagclass.ConstantFieldReceiverNonNull.AnotherClass?: TyTag;

// Tclass.ConstantFieldReceiverNonNull.AnotherClass? Tag
axiom Tag(Tclass.ConstantFieldReceiverNonNull.AnotherClass?())
     == Tagclass.ConstantFieldReceiverNonNull.AnotherClass?
   && TagFamily(Tclass.ConstantFieldReceiverNonNull.AnotherClass?())
     == tytagFamily$AnotherClass;

// Box/unbox axiom for Tclass.ConstantFieldReceiverNonNull.AnotherClass?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.AnotherClass?()) } 
  $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.AnotherClass?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ConstantFieldReceiverNonNull.AnotherClass?()));

// AnotherClass: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ConstantFieldReceiverNonNull.AnotherClass?()) } 
  $Is($o, Tclass.ConstantFieldReceiverNonNull.AnotherClass?())
     <==> $o == null || dtype($o) == Tclass.ConstantFieldReceiverNonNull.AnotherClass?());

// AnotherClass: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.AnotherClass?(), $h) } 
  $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.AnotherClass?(), $h)
     <==> $o == null || read($h, $o, alloc));

function ConstantFieldReceiverNonNull.AnotherClass.u(this: ref) : int;

// AnotherClass.u: Type axiom
axiom (forall $o: ref :: 
  { ConstantFieldReceiverNonNull.AnotherClass.u($o) } 
  $Is(ConstantFieldReceiverNonNull.AnotherClass.u($o), TInt));

// AnotherClass.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { ConstantFieldReceiverNonNull.AnotherClass.u($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(ConstantFieldReceiverNonNull.AnotherClass.u($o), TInt, $h));

function Tclass.ConstantFieldReceiverNonNull.AnotherClass() : Ty;

const unique Tagclass.ConstantFieldReceiverNonNull.AnotherClass: TyTag;

// Tclass.ConstantFieldReceiverNonNull.AnotherClass Tag
axiom Tag(Tclass.ConstantFieldReceiverNonNull.AnotherClass())
     == Tagclass.ConstantFieldReceiverNonNull.AnotherClass
   && TagFamily(Tclass.ConstantFieldReceiverNonNull.AnotherClass())
     == tytagFamily$AnotherClass;

// Box/unbox axiom for Tclass.ConstantFieldReceiverNonNull.AnotherClass
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.AnotherClass()) } 
  $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.AnotherClass())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ConstantFieldReceiverNonNull.AnotherClass()));

// ConstantFieldReceiverNonNull.AnotherClass: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.ConstantFieldReceiverNonNull.AnotherClass()) } 
  $Is(c#0, Tclass.ConstantFieldReceiverNonNull.AnotherClass())
     <==> $Is(c#0, Tclass.ConstantFieldReceiverNonNull.AnotherClass?()) && c#0 != null);

// ConstantFieldReceiverNonNull.AnotherClass: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.AnotherClass(), $h) } 
  $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.AnotherClass(), $h)
     <==> $IsAlloc(c#0, Tclass.ConstantFieldReceiverNonNull.AnotherClass?(), $h));

const unique class.ConstantFieldReceiverNonNull.__default: ClassName;

function Tclass.ConstantFieldReceiverNonNull.__default() : Ty;

const unique Tagclass.ConstantFieldReceiverNonNull.__default: TyTag;

// Tclass.ConstantFieldReceiverNonNull.__default Tag
axiom Tag(Tclass.ConstantFieldReceiverNonNull.__default())
     == Tagclass.ConstantFieldReceiverNonNull.__default
   && TagFamily(Tclass.ConstantFieldReceiverNonNull.__default())
     == tytagFamily$_default;

// Box/unbox axiom for Tclass.ConstantFieldReceiverNonNull.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.__default()) } 
  $IsBox(bx, Tclass.ConstantFieldReceiverNonNull.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ConstantFieldReceiverNonNull.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ConstantFieldReceiverNonNull.__default()) } 
  $Is($o, Tclass.ConstantFieldReceiverNonNull.__default())
     <==> $o == null || dtype($o) == Tclass.ConstantFieldReceiverNonNull.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.__default(), $h) } 
  $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.__default(), $h)
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

const unique tytagFamily$Node: TyTagFamily;

const unique tytagFamily$Modifies: TyTagFamily;

const unique tytagFamily$AllocatedTests: TyTagFamily;

const unique tytagFamily$Lindgren: TyTagFamily;

const unique tytagFamily$InitCalls: TyTagFamily;

const unique tytagFamily$SomeType: TyTagFamily;

const unique tytagFamily$Test: TyTagFamily;

const unique tytagFamily$AttributeTests: TyTagFamily;

const unique tytagFamily$QuiteFinite: TyTagFamily;

const unique tytagFamily$GT: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Six: TyTagFamily;

const unique tytagFamily$Trait: TyTagFamily;

const unique tytagFamily$Class: TyTagFamily;

const unique tytagFamily$AnotherClass: TyTagFamily;

const unique field$next: NameFamily;

const unique field$x: NameFamily;

const unique field$z: NameFamily;

const unique field$p: NameFamily;

const unique field$f: NameFamily;

const unique field$y: NameFamily;

axiom (forall $o: ref :: 
  { $Is($o, Tclass.ConstantFieldReceiverNonNull.Class?()) } 
  $o != null && $Is($o, Tclass.ConstantFieldReceiverNonNull.Class?())
     ==> $Is($o, Tclass.ConstantFieldReceiverNonNull.Trait()));

axiom (forall $o: ref, $heap: Heap :: 
  { $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.Class?(), $heap) } 
  $o != null && $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.Class?(), $heap)
     ==> $IsAlloc($o, Tclass.ConstantFieldReceiverNonNull.Trait(), $heap));
