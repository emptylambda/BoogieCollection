// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy -print:./Streams.bpl

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

function Tclass._System.___hFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc2: TyTag;

// Tclass._System.___hFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == Tagclass._System.___hFunc2
     && TagFamily(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == tytagFamily$_#Func2);

// Tclass._System.___hFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_0(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$T0);

function Tclass._System.___hFunc2_0(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_1(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$T1);

function Tclass._System.___hFunc2_1(Ty) : Ty;

// Tclass._System.___hFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hFunc2_2(Tclass._System.___hFunc2(#$T0, #$T1, #$R)) == #$R);

function Tclass._System.___hFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc2(#$T0, #$T1, #$R)));

function Handle2([Heap,Box,Box]Box, [Heap,Box,Box]bool, [Heap,Box,Box]Set Box) : HandleType;

function Apply2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Box;

function Requires2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : bool;

function Reads2(Ty, Ty, Ty, Heap, HandleType, Box, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box :: 
  { Apply2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) } 
  Apply2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) == h[heap, bx0, bx1]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box :: 
  { Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1) } 
  r[heap, bx0, bx1] ==> Requires2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box]Box, 
    r: [Heap,Box,Box]bool, 
    rd: [Heap,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx: Box :: 
  { Reads2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1)[bx] } 
  Reads2(t0, t1, t2, heap, Handle2(h, r, rd), bx0, bx1)[bx]
     == rd[heap, bx0, bx1][bx]);

function {:inline} Requires2#canCall(t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box) : bool
{
  true
}

function {:inline} Reads2#canCall(t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box) : bool
{
  true
}

// frame axiom for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Reads2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads2(t0, t1, t2, h0, f, bx0, bx1) == Reads2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Reads2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Reads2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads2(t0, t1, t2, h0, f, bx0, bx1) == Reads2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Requires2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires2(t0, t1, t2, h0, f, bx0, bx1) == Requires2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Requires2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires2(t0, t1, t2, h0, f, bx0, bx1) == Requires2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Apply2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Apply2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h0, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply2(t0, t1, t2, h0, f, bx0, bx1) == Apply2(t0, t1, t2, h1, f, bx0, bx1));

// frame axiom for Apply2
axiom (forall t0: Ty, t1: Ty, t2: Ty, h0: Heap, h1: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { $HeapSucc(h0, h1), Apply2(t0, t1, t2, h1, f, bx0, bx1) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads2(t0, t1, t2, h1, f, bx0, bx1)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply2(t0, t1, t2, h0, f, bx0, bx1) == Apply2(t0, t1, t2, h1, f, bx0, bx1));

// empty-reads property for Reads2 
axiom (forall t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), $IsGoodHeap(heap) } 
    { Reads2(t0, t1, t2, heap, f, bx0, bx1) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
     ==> (Set#Equal(Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), Set#Empty(): Set Box)
       <==> Set#Equal(Reads2(t0, t1, t2, heap, f, bx0, bx1), Set#Empty(): Set Box)));

// empty-reads property for Requires2
axiom (forall t0: Ty, t1: Ty, t2: Ty, heap: Heap, f: HandleType, bx0: Box, bx1: Box :: 
  { Requires2(t0, t1, t2, $OneHeap, f, bx0, bx1), $IsGoodHeap(heap) } 
    { Requires2(t0, t1, t2, heap, f, bx0, bx1) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && Set#Equal(Reads2(t0, t1, t2, $OneHeap, f, bx0, bx1), Set#Empty(): Set Box)
     ==> Requires2(t0, t1, t2, $OneHeap, f, bx0, bx1)
       == Requires2(t0, t1, t2, heap, f, bx0, bx1));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty :: 
  { $Is(f, Tclass._System.___hFunc2(t0, t1, t2)) } 
  $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
     <==> (forall h: Heap, bx0: Box, bx1: Box :: 
      { Apply2(t0, t1, t2, h, f, bx0, bx1) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && Requires2(t0, t1, t2, h, f, bx0, bx1)
         ==> $IsBox(Apply2(t0, t1, t2, h, f, bx0, bx1), t2)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, u0: Ty, u1: Ty, u2: Ty :: 
  { $Is(f, Tclass._System.___hFunc2(t0, t1, t2)), $Is(f, Tclass._System.___hFunc2(u0, u1, u2)) } 
  $Is(f, Tclass._System.___hFunc2(t0, t1, t2))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, u1) } { $IsBox(bx, t1) } 
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, t2) } { $IsBox(bx, u2) } 
        $IsBox(bx, t2) ==> $IsBox(bx, u2))
     ==> $Is(f, Tclass._System.___hFunc2(u0, u1, u2)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h)
       <==> (forall bx0: Box, bx1: Box :: 
        { Apply2(t0, t1, t2, h, f, bx0, bx1) } { Reads2(t0, t1, t2, h, f, bx0, bx1) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && Requires2(t0, t1, t2, h, f, bx0, bx1)
           ==> (forall r: ref :: 
            { Reads2(t0, t1, t2, h, f, bx0, bx1)[$Box(r)] } 
            r != null && Reads2(t0, t1, t2, h, f, bx0, bx1)[$Box(r)] ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc2(t0, t1, t2), h)
     ==> (forall bx0: Box, bx1: Box :: 
      { Apply2(t0, t1, t2, h, f, bx0, bx1) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && Requires2(t0, t1, t2, h, f, bx0, bx1)
         ==> $IsAllocBox(Apply2(t0, t1, t2, h, f, bx0, bx1), t2, h)));

function Tclass._System.___hPartialFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc2: TyTag;

// Tclass._System.___hPartialFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       == Tagclass._System.___hPartialFunc2
     && TagFamily(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       == tytagFamily$_#PartialFunc2);

// Tclass._System.___hPartialFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_0(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc2_0(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_1(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc2_1(Ty) : Ty;

// Tclass._System.___hPartialFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hPartialFunc2_2(Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     == #$R);

function Tclass._System.___hPartialFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)));

// _System._#PartialFunc2: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc2(#$T0, #$T1, #$R))
       && (forall x0#0: Box, x1#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Set#Equal(Reads2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0), Set#Empty(): Set Box)));

// _System._#PartialFunc2: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc2(#$T0, #$T1, #$R), $h));

function Tclass._System.___hTotalFunc2(Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc2: TyTag;

// Tclass._System.___hTotalFunc2 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tag(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
       == Tagclass._System.___hTotalFunc2
     && TagFamily(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
       == tytagFamily$_#TotalFunc2);

// Tclass._System.___hTotalFunc2 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_0(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc2_0(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_1(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc2_1(Ty) : Ty;

// Tclass._System.___hTotalFunc2 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R) } 
  Tclass._System.___hTotalFunc2_2(Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     == #$R);

function Tclass._System.___hTotalFunc2_2(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc2
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)));

// _System._#TotalFunc2: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R))
       && (forall x0#0: Box, x1#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1)
           ==> Requires2(#$T0, #$T1, #$R, $OneHeap, f#0, x0#0, x1#0)));

// _System._#TotalFunc2: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc2(#$T0, #$T1, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc2(#$T0, #$T1, #$R), $h));

function Tclass._System.___hFunc3(Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc3: TyTag;

// Tclass._System.___hFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tag(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
       == Tagclass._System.___hFunc3
     && TagFamily(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
       == tytagFamily$_#Func3);

// Tclass._System.___hFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hFunc3_0(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hFunc3_0(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hFunc3_1(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hFunc3_1(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hFunc3_2(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hFunc3_2(Ty) : Ty;

// Tclass._System.___hFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hFunc3_3(Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R)));

function Handle3([Heap,Box,Box,Box]Box, [Heap,Box,Box,Box]bool, [Heap,Box,Box,Box]Set Box)
   : HandleType;

function Apply3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : Box;

function Requires3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : bool;

function Reads3(Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { Apply3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2) } 
  Apply3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)
     == h[heap, bx0, bx1, bx2]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { Requires3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2) } 
  r[heap, bx0, bx1, bx2]
     ==> Requires3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx: Box :: 
  { Reads3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)[bx] } 
  Reads3(t0, t1, t2, t3, heap, Handle3(h, r, rd), bx0, bx1, bx2)[bx]
     == rd[heap, bx0, bx1, bx2][bx]);

function {:inline} Requires3#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box)
   : bool
{
  true
}

function {:inline} Reads3#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box)
   : bool
{
  true
}

// frame axiom for Reads3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Reads3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Requires3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Requires3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Apply3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// frame axiom for Apply3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { $HeapSucc(h0, h1), Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply3(t0, t1, t2, t3, h0, f, bx0, bx1, bx2)
       == Apply3(t0, t1, t2, t3, h1, f, bx0, bx1, bx2));

// empty-reads property for Reads3 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), $IsGoodHeap(heap) } 
    { Reads3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
     ==> (Set#Equal(Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), Set#Empty(): Set Box)
       <==> Set#Equal(Reads3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2), Set#Empty(): Set Box)));

// empty-reads property for Requires3
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box :: 
  { Requires3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), $IsGoodHeap(heap) } 
    { Requires3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && Set#Equal(Reads3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2), Set#Empty(): Set Box)
     ==> Requires3(t0, t1, t2, t3, $OneHeap, f, bx0, bx1, bx2)
       == Requires3(t0, t1, t2, t3, heap, f, bx0, bx1, bx2));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty :: 
  { $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3)) } 
  $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box :: 
      { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
         ==> $IsBox(Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2), t3)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, u0: Ty, u1: Ty, u2: Ty, u3: Ty :: 
  { $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3)), $Is(f, Tclass._System.___hFunc3(u0, u1, u2, u3)) } 
  $Is(f, Tclass._System.___hFunc3(t0, t1, t2, t3))
       && (forall bx: Box :: 
        { $IsBox(bx, u0) } { $IsBox(bx, t0) } 
        $IsBox(bx, u0) ==> $IsBox(bx, t0))
       && (forall bx: Box :: 
        { $IsBox(bx, u1) } { $IsBox(bx, t1) } 
        $IsBox(bx, u1) ==> $IsBox(bx, t1))
       && (forall bx: Box :: 
        { $IsBox(bx, u2) } { $IsBox(bx, t2) } 
        $IsBox(bx, u2) ==> $IsBox(bx, t2))
       && (forall bx: Box :: 
        { $IsBox(bx, t3) } { $IsBox(bx, u3) } 
        $IsBox(bx, t3) ==> $IsBox(bx, u3))
     ==> $Is(f, Tclass._System.___hFunc3(u0, u1, u2, u3)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box :: 
        { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) } 
          { Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && 
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
           ==> (forall r: ref :: 
            { Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)[$Box(r)] } 
            r != null && Reads3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc3(t0, t1, t2, t3), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box :: 
      { Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && Requires3(t0, t1, t2, t3, h, f, bx0, bx1, bx2)
         ==> $IsAllocBox(Apply3(t0, t1, t2, t3, h, f, bx0, bx1, bx2), t3, h)));

function Tclass._System.___hPartialFunc3(Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc3: TyTag;

// Tclass._System.___hPartialFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tag(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
       == Tagclass._System.___hPartialFunc3
     && TagFamily(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
       == tytagFamily$_#PartialFunc3);

// Tclass._System.___hPartialFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hPartialFunc3_0(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc3_0(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hPartialFunc3_1(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc3_1(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hPartialFunc3_2(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc3_2(Ty) : Ty;

// Tclass._System.___hPartialFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hPartialFunc3_3(Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hPartialFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)));

// _System._#PartialFunc3: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1) && $IsBox(x2#0, #$T2)
           ==> Set#Equal(Reads3(#$T0, #$T1, #$T2, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc3: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc3(#$T0, #$T1, #$T2, #$R), $h));

function Tclass._System.___hTotalFunc3(Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc3: TyTag;

// Tclass._System.___hTotalFunc3 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tag(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
       == Tagclass._System.___hTotalFunc3
     && TagFamily(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
       == tytagFamily$_#TotalFunc3);

// Tclass._System.___hTotalFunc3 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hTotalFunc3_0(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc3_0(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hTotalFunc3_1(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc3_1(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hTotalFunc3_2(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc3_2(Ty) : Ty;

// Tclass._System.___hTotalFunc3 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R) } 
  Tclass._System.___hTotalFunc3_3(Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     == #$R);

function Tclass._System.___hTotalFunc3_3(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)));

// _System._#TotalFunc3: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box :: 
        $IsBox(x0#0, #$T0) && $IsBox(x1#0, #$T1) && $IsBox(x2#0, #$T2)
           ==> Requires3(#$T0, #$T1, #$T2, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0)));

// _System._#TotalFunc3: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc3(#$T0, #$T1, #$T2, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc3(#$T0, #$T1, #$T2, #$R), $h));

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

// Constructor function declaration
function #_module.Stream.Nil() : DatatypeType;

const unique ##_module.Stream.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.Stream.Nil()) == ##_module.Stream.Nil;

function _module.Stream.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Stream.Nil_q(d) } 
  _module.Stream.Nil_q(d) <==> DatatypeCtorId(d) == ##_module.Stream.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Stream.Nil_q(d) } 
  _module.Stream.Nil_q(d) ==> d == #_module.Stream.Nil());

function Tclass._module.Stream(Ty) : Ty;

const unique Tagclass._module.Stream: TyTag;

// Tclass._module.Stream Tag
axiom (forall _module.Stream$T: Ty :: 
  { Tclass._module.Stream(_module.Stream$T) } 
  Tag(Tclass._module.Stream(_module.Stream$T)) == Tagclass._module.Stream
     && TagFamily(Tclass._module.Stream(_module.Stream$T)) == tytagFamily$Stream);

// Tclass._module.Stream injectivity 0
axiom (forall _module.Stream$T: Ty :: 
  { Tclass._module.Stream(_module.Stream$T) } 
  Tclass._module.Stream_0(Tclass._module.Stream(_module.Stream$T))
     == _module.Stream$T);

function Tclass._module.Stream_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Stream
axiom (forall _module.Stream$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Stream(_module.Stream$T)) } 
  $IsBox(bx, Tclass._module.Stream(_module.Stream$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Stream(_module.Stream$T)));

// Constructor $Is
axiom (forall _module.Stream$T: Ty :: 
  { $Is(#_module.Stream.Nil(), Tclass._module.Stream(_module.Stream$T)) } 
  $Is(#_module.Stream.Nil(), Tclass._module.Stream(_module.Stream$T)));

// Constructor $IsAlloc
axiom (forall _module.Stream$T: Ty, $h: Heap :: 
  { $IsAlloc(#_module.Stream.Nil(), Tclass._module.Stream(_module.Stream$T), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.Stream.Nil(), Tclass._module.Stream(_module.Stream$T), $h));

// Constructor function declaration
function #_module.Stream.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.Stream.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#18#0#0: Box, a#18#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#18#0#0, a#18#1#0) } 
  DatatypeCtorId(#_module.Stream.Cons(a#18#0#0, a#18#1#0))
     == ##_module.Stream.Cons);

function _module.Stream.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Stream.Cons_q(d) } 
  _module.Stream.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.Stream.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Stream.Cons_q(d) } 
  _module.Stream.Cons_q(d)
     ==> (exists a#19#0#0: Box, a#19#1#0: DatatypeType :: 
      d == #_module.Stream.Cons(a#19#0#0, a#19#1#0)));

// Constructor $Is
axiom (forall _module.Stream$T: Ty, a#20#0#0: Box, a#20#1#0: DatatypeType :: 
  { $Is(#_module.Stream.Cons(a#20#0#0, a#20#1#0), 
      Tclass._module.Stream(_module.Stream$T)) } 
  $Is(#_module.Stream.Cons(a#20#0#0, a#20#1#0), 
      Tclass._module.Stream(_module.Stream$T))
     <==> $IsBox(a#20#0#0, _module.Stream$T)
       && $Is(a#20#1#0, Tclass._module.Stream(_module.Stream$T)));

// Constructor $IsAlloc
axiom (forall _module.Stream$T: Ty, a#21#0#0: Box, a#21#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Stream.Cons(a#21#0#0, a#21#1#0), 
      Tclass._module.Stream(_module.Stream$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Stream.Cons(a#21#0#0, a#21#1#0), 
        Tclass._module.Stream(_module.Stream$T), 
        $h)
       <==> $IsAllocBox(a#21#0#0, _module.Stream$T, $h)
         && $IsAlloc(a#21#1#0, Tclass._module.Stream(_module.Stream$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Stream$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Stream.head(d), _module.Stream$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Stream.Cons_q(d)
       && $IsAlloc(d, Tclass._module.Stream(_module.Stream$T), $h)
     ==> $IsAllocBox(_module.Stream.head(d), _module.Stream$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Stream$T: Ty, $h: Heap :: 
  { $IsAlloc(_module.Stream.tail(d), Tclass._module.Stream(_module.Stream$T), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Stream.Cons_q(d)
       && $IsAlloc(d, Tclass._module.Stream(_module.Stream$T), $h)
     ==> $IsAlloc(_module.Stream.tail(d), Tclass._module.Stream(_module.Stream$T), $h));

function _module.Stream.head(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#22#0#0: Box, a#22#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#22#0#0, a#22#1#0) } 
  _module.Stream.head(#_module.Stream.Cons(a#22#0#0, a#22#1#0)) == a#22#0#0);

function _module.Stream.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#23#0#0: Box, a#23#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#23#0#0, a#23#1#0) } 
  _module.Stream.tail(#_module.Stream.Cons(a#23#0#0, a#23#1#0)) == a#23#1#0);

// Depth-one case-split function
function $IsA#_module.Stream(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Stream(d) } 
  $IsA#_module.Stream(d) ==> _module.Stream.Nil_q(d) || _module.Stream.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Stream$T: Ty, d: DatatypeType :: 
  { _module.Stream.Cons_q(d), $Is(d, Tclass._module.Stream(_module.Stream$T)) } 
    { _module.Stream.Nil_q(d), $Is(d, Tclass._module.Stream(_module.Stream$T)) } 
  $Is(d, Tclass._module.Stream(_module.Stream$T))
     ==> _module.Stream.Nil_q(d) || _module.Stream.Cons_q(d));

function $Eq#_module.Stream(Ty, Ty, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Stream(_module.Stream$T#l))
       && $Is(d1, Tclass._module.Stream(_module.Stream$T#r))
     ==> ($Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1)
       <==> (_module.Stream.Nil_q(d0) && _module.Stream.Nil_q(d1))
         || (
          _module.Stream.Cons_q(d0)
           && _module.Stream.Cons_q(d1)
           && (_module.Stream.Cons_q(d0) && _module.Stream.Cons_q(d1)
             ==> _module.Stream.head(d0) == _module.Stream.head(d1)
               && $Eq#_module.Stream(_module.Stream$T#l, 
                _module.Stream$T#r, 
                ly, 
                _module.Stream.tail(d0), 
                _module.Stream.tail(d1))))));

// Unbump layer co-equality axiom
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1)
     <==> $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, ly, d0, d1));

// Equality for codatatypes
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1)
     <==> d0 == d1);

function $PrefixEq#_module.Stream(Ty, Ty, Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.Stream(_module.Stream$T#l))
       && $Is(d1, Tclass._module.Stream(_module.Stream$T#r))
     ==> ($PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (_module.Stream.Nil_q(d0) && _module.Stream.Nil_q(d1))
             || (
              _module.Stream.Cons_q(d0)
               && _module.Stream.Cons_q(d1)
               && (_module.Stream.Cons_q(d0) && _module.Stream.Cons_q(d1)
                 ==> _module.Stream.head(d0) == _module.Stream.head(d1)
                   && $PrefixEq#_module.Stream(_module.Stream$T#l, 
                    _module.Stream$T#r, 
                    ORD#Minus(k, ORD#FromNat(1)), 
                    ly, 
                    _module.Stream.tail(d0), 
                    _module.Stream.tail(d1)))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k)
           ==> $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k
         ==> $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, $LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType, 
    m: Box :: 
  { $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1), $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, m, $LS(ly), d0, d1) } 
  ORD#Less(k, m)
       && $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall _module.Stream$T#l: Ty, 
    _module.Stream$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1) } 
  d0 == d1
     ==> $PrefixEq#_module.Stream(_module.Stream$T#l, _module.Stream$T#r, k, $LS(ly), d0, d1));

const unique class._module.Stream: ClassName;

const #$X: Ty;

const unique class._module.X: ClassName;

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

// function declaration for _module._default.append
function _module.__default.append(_module._default.append$_T0: Ty, 
    $ly: LayerType, 
    M#0: DatatypeType, 
    N#0: DatatypeType)
   : DatatypeType;

function _module.__default.append#canCall(_module._default.append$_T0: Ty, M#0: DatatypeType, N#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.append$_T0: Ty, 
    $ly: LayerType, 
    M#0: DatatypeType, 
    N#0: DatatypeType :: 
  { _module.__default.append(_module._default.append$_T0, $LS($ly), M#0, N#0) } 
  _module.__default.append(_module._default.append$_T0, $LS($ly), M#0, N#0)
     == _module.__default.append(_module._default.append$_T0, $ly, M#0, N#0));

// fuel synonym axiom
axiom (forall _module._default.append$_T0: Ty, 
    $ly: LayerType, 
    M#0: DatatypeType, 
    N#0: DatatypeType :: 
  { _module.__default.append(_module._default.append$_T0, AsFuelBottom($ly), M#0, N#0) } 
  _module.__default.append(_module._default.append$_T0, $ly, M#0, N#0)
     == _module.__default.append(_module._default.append$_T0, $LZ, M#0, N#0));

// consequence axiom for _module.__default.append
axiom 10 <= $FunctionContextHeight
   ==> (forall _module._default.append$_T0: Ty, 
      $ly: LayerType, 
      M#0: DatatypeType, 
      N#0: DatatypeType :: 
    { _module.__default.append(_module._default.append$_T0, $ly, M#0, N#0) } 
    _module.__default.append#canCall(_module._default.append$_T0, M#0, N#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(M#0, Tclass._module.Stream(_module._default.append$_T0))
           && $Is(N#0, Tclass._module.Stream(_module._default.append$_T0)))
       ==> $Is(_module.__default.append(_module._default.append$_T0, $ly, M#0, N#0), 
        Tclass._module.Stream(_module._default.append$_T0)));

function _module.__default.append#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.append
axiom (forall _module._default.append$_T0: Ty, 
    $ly: LayerType, 
    M#0: DatatypeType, 
    N#0: DatatypeType :: 
  { _module.__default.append#requires(_module._default.append$_T0, $ly, M#0, N#0) } 
  $Is(M#0, Tclass._module.Stream(_module._default.append$_T0))
       && $Is(N#0, Tclass._module.Stream(_module._default.append$_T0))
     ==> _module.__default.append#requires(_module._default.append$_T0, $ly, M#0, N#0)
       == true);

// definition axiom for _module.__default.append (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall _module._default.append$_T0: Ty, 
      $ly: LayerType, 
      M#0: DatatypeType, 
      N#0: DatatypeType :: 
    { _module.__default.append(_module._default.append$_T0, $LS($ly), M#0, N#0) } 
    _module.__default.append#canCall(_module._default.append$_T0, M#0, N#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(M#0, Tclass._module.Stream(_module._default.append$_T0))
           && $Is(N#0, Tclass._module.Stream(_module._default.append$_T0)))
       ==> (!_module.Stream.Nil_q(M#0)
           ==> (var M'#1 := _module.Stream.tail(M#0); 
            _module.__default.append#canCall(_module._default.append$_T0, M'#1, N#0)))
         && _module.__default.append(_module._default.append$_T0, $LS($ly), M#0, N#0)
           == (if _module.Stream.Nil_q(M#0)
             then N#0
             else (var M'#0 := _module.Stream.tail(M#0); 
              (var t#0 := _module.Stream.head(M#0); 
                #_module.Stream.Cons(t#0, _module.__default.append(_module._default.append$_T0, $ly, M'#0, N#0))))));

procedure CheckWellformed$$_module.__default.append(_module._default.append$_T0: Ty, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(_module._default.append$_T0)), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(_module._default.append$_T0)));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.append(_module._default.append$_T0: Ty, M#0: DatatypeType, N#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var M'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var t#Z#0: Box;
  var let#1#0#0: Box;
  var ##M#0: DatatypeType;
  var ##N#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function append
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(8,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.append(_module._default.append$_T0, $LS($LZ), M#0, N#0), 
          Tclass._module.Stream(_module._default.append$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (M#0 == #_module.Stream.Nil())
        {
            assume _module.__default.append(_module._default.append$_T0, $LS($LZ), M#0, N#0) == N#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.append(_module._default.append$_T0, $LS($LZ), M#0, N#0), 
              Tclass._module.Stream(_module._default.append$_T0));
        }
        else if (M#0 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.append$_T0);
            assume $Is(_mcc#1#0, Tclass._module.Stream(_module._default.append$_T0));
            havoc M'#Z#0;
            assume $Is(M'#Z#0, Tclass._module.Stream(_module._default.append$_T0));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(_module._default.append$_T0));
            assume M'#Z#0 == let#0#0#0;
            havoc t#Z#0;
            assume $IsBox(t#Z#0, _module._default.append$_T0);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, _module._default.append$_T0);
            assume t#Z#0 == let#1#0#0;
            ##M#0 := M'#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##M#0, Tclass._module.Stream(_module._default.append$_T0), $Heap);
            ##N#0 := N#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##N#0, Tclass._module.Stream(_module._default.append$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.append#canCall(_module._default.append$_T0, M'#Z#0, N#0);
            assume _module.__default.append(_module._default.append$_T0, $LS($LZ), M#0, N#0)
               == #_module.Stream.Cons(t#Z#0, 
                _module.__default.append(_module._default.append$_T0, $LS($LZ), M'#Z#0, N#0));
            assume _module.__default.append#canCall(_module._default.append$_T0, M'#Z#0, N#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.append(_module._default.append$_T0, $LS($LZ), M#0, N#0), 
              Tclass._module.Stream(_module._default.append$_T0));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.f
function _module.__default.f(x#0: Box) : Box;

function _module.__default.f#canCall(x#0: Box) : bool;

// consequence axiom for _module.__default.f
axiom 1 <= $FunctionContextHeight
   ==> (forall x#0: Box :: 
    { _module.__default.f(x#0) } 
    _module.__default.f#canCall(x#0)
         || (1 != $FunctionContextHeight && $IsBox(x#0, #$X))
       ==> $IsBox(_module.__default.f(x#0), #$X));

function _module.__default.f#requires(Box) : bool;

// #requires axiom for _module.__default.f
axiom (forall x#0: Box :: 
  { _module.__default.f#requires(x#0) } 
  $IsBox(x#0, #$X) ==> _module.__default.f#requires(x#0) == true);

procedure CheckWellformed$$_module.__default.f(x#0: Box where $IsBox(x#0, #$X));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.g
function _module.__default.g(x#0: Box) : Box;

function _module.__default.g#canCall(x#0: Box) : bool;

// consequence axiom for _module.__default.g
axiom 2 <= $FunctionContextHeight
   ==> (forall x#0: Box :: 
    { _module.__default.g(x#0) } 
    _module.__default.g#canCall(x#0)
         || (2 != $FunctionContextHeight && $IsBox(x#0, #$X))
       ==> $IsBox(_module.__default.g(x#0), #$X));

function _module.__default.g#requires(Box) : bool;

// #requires axiom for _module.__default.g
axiom (forall x#0: Box :: 
  { _module.__default.g#requires(x#0) } 
  $IsBox(x#0, #$X) ==> _module.__default.g#requires(x#0) == true);

procedure CheckWellformed$$_module.__default.g(x#0: Box where $IsBox(x#0, #$X));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.map_f
function _module.__default.map__f($ly: LayerType, M#0: DatatypeType) : DatatypeType;

function _module.__default.map__f#canCall(M#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__f($LS($ly), M#0) } 
  _module.__default.map__f($LS($ly), M#0) == _module.__default.map__f($ly, M#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__f(AsFuelBottom($ly), M#0) } 
  _module.__default.map__f($ly, M#0) == _module.__default.map__f($LZ, M#0));

// consequence axiom for _module.__default.map__f
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.map__f($ly, M#0) } 
    _module.__default.map__f#canCall(M#0)
         || (4 != $FunctionContextHeight && $Is(M#0, Tclass._module.Stream(#$X)))
       ==> $Is(_module.__default.map__f($ly, M#0), Tclass._module.Stream(#$X)));

function _module.__default.map__f#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.map__f
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__f#requires($ly, M#0) } 
  $Is(M#0, Tclass._module.Stream(#$X))
     ==> _module.__default.map__f#requires($ly, M#0) == true);

// definition axiom for _module.__default.map__f (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.map__f($LS($ly), M#0) } 
    _module.__default.map__f#canCall(M#0)
         || (4 != $FunctionContextHeight && $Is(M#0, Tclass._module.Stream(#$X)))
       ==> (!_module.Stream.Nil_q(M#0)
           ==> (var N#1 := _module.Stream.tail(M#0); 
            (var x#1 := _module.Stream.head(M#0); 
              _module.__default.f#canCall(x#1) && _module.__default.map__f#canCall(N#1))))
         && _module.__default.map__f($LS($ly), M#0)
           == (if _module.Stream.Nil_q(M#0)
             then #_module.Stream.Nil()
             else (var N#0 := _module.Stream.tail(M#0); 
              (var x#0 := _module.Stream.head(M#0); 
                #_module.Stream.Cons(_module.__default.f(x#0), _module.__default.map__f($ly, N#0))))));

procedure CheckWellformed$$_module.__default.map__f(M#0: DatatypeType where $Is(M#0, Tclass._module.Stream(#$X)));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.map__f(M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var N#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: Box;
  var let#1#0#0: Box;
  var ##x#0: Box;
  var ##M#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function map_f
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(22,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.map__f($LS($LZ), M#0), Tclass._module.Stream(#$X));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (M#0 == #_module.Stream.Nil())
        {
            assume _module.__default.map__f($LS($LZ), M#0) == Lit(#_module.Stream.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.map__f($LS($LZ), M#0), Tclass._module.Stream(#$X));
        }
        else if (M#0 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, #$X);
            assume $Is(_mcc#1#0, Tclass._module.Stream(#$X));
            havoc N#Z#0;
            assume $Is(N#Z#0, Tclass._module.Stream(#$X));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(#$X));
            assume N#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $IsBox(x#Z#0, #$X);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, #$X);
            assume x#Z#0 == let#1#0#0;
            ##x#0 := x#Z#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#0, #$X, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.f#canCall(x#Z#0);
            ##M#0 := N#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##M#0, Tclass._module.Stream(#$X), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.map__f#canCall(N#Z#0);
            assume _module.__default.map__f($LS($LZ), M#0)
               == #_module.Stream.Cons(_module.__default.f(x#Z#0), _module.__default.map__f($LS($LZ), N#Z#0));
            assume _module.__default.f#canCall(x#Z#0) && _module.__default.map__f#canCall(N#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.map__f($LS($LZ), M#0), Tclass._module.Stream(#$X));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.map_g
function _module.__default.map__g($ly: LayerType, M#0: DatatypeType) : DatatypeType;

function _module.__default.map__g#canCall(M#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__g($LS($ly), M#0) } 
  _module.__default.map__g($LS($ly), M#0) == _module.__default.map__g($ly, M#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__g(AsFuelBottom($ly), M#0) } 
  _module.__default.map__g($ly, M#0) == _module.__default.map__g($LZ, M#0));

// consequence axiom for _module.__default.map__g
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.map__g($ly, M#0) } 
    _module.__default.map__g#canCall(M#0)
         || (5 != $FunctionContextHeight && $Is(M#0, Tclass._module.Stream(#$X)))
       ==> $Is(_module.__default.map__g($ly, M#0), Tclass._module.Stream(#$X)));

function _module.__default.map__g#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.map__g
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__g#requires($ly, M#0) } 
  $Is(M#0, Tclass._module.Stream(#$X))
     ==> _module.__default.map__g#requires($ly, M#0) == true);

// definition axiom for _module.__default.map__g (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.map__g($LS($ly), M#0) } 
    _module.__default.map__g#canCall(M#0)
         || (5 != $FunctionContextHeight && $Is(M#0, Tclass._module.Stream(#$X)))
       ==> (!_module.Stream.Nil_q(M#0)
           ==> (var N#1 := _module.Stream.tail(M#0); 
            (var x#1 := _module.Stream.head(M#0); 
              _module.__default.g#canCall(x#1) && _module.__default.map__g#canCall(N#1))))
         && _module.__default.map__g($LS($ly), M#0)
           == (if _module.Stream.Nil_q(M#0)
             then #_module.Stream.Nil()
             else (var N#0 := _module.Stream.tail(M#0); 
              (var x#0 := _module.Stream.head(M#0); 
                #_module.Stream.Cons(_module.__default.g(x#0), _module.__default.map__g($ly, N#0))))));

procedure CheckWellformed$$_module.__default.map__g(M#0: DatatypeType where $Is(M#0, Tclass._module.Stream(#$X)));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.map__g(M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var N#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: Box;
  var let#1#0#0: Box;
  var ##x#0: Box;
  var ##M#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function map_g
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(29,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.map__g($LS($LZ), M#0), Tclass._module.Stream(#$X));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (M#0 == #_module.Stream.Nil())
        {
            assume _module.__default.map__g($LS($LZ), M#0) == Lit(#_module.Stream.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.map__g($LS($LZ), M#0), Tclass._module.Stream(#$X));
        }
        else if (M#0 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, #$X);
            assume $Is(_mcc#1#0, Tclass._module.Stream(#$X));
            havoc N#Z#0;
            assume $Is(N#Z#0, Tclass._module.Stream(#$X));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(#$X));
            assume N#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $IsBox(x#Z#0, #$X);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, #$X);
            assume x#Z#0 == let#1#0#0;
            ##x#0 := x#Z#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#0, #$X, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.g#canCall(x#Z#0);
            ##M#0 := N#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##M#0, Tclass._module.Stream(#$X), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.map__g#canCall(N#Z#0);
            assume _module.__default.map__g($LS($LZ), M#0)
               == #_module.Stream.Cons(_module.__default.g(x#Z#0), _module.__default.map__g($LS($LZ), N#Z#0));
            assume _module.__default.g#canCall(x#Z#0) && _module.__default.map__g#canCall(N#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.map__g($LS($LZ), M#0), Tclass._module.Stream(#$X));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.map_fg
function _module.__default.map__fg($ly: LayerType, M#0: DatatypeType) : DatatypeType;

function _module.__default.map__fg#canCall(M#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__fg($LS($ly), M#0) } 
  _module.__default.map__fg($LS($ly), M#0) == _module.__default.map__fg($ly, M#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__fg(AsFuelBottom($ly), M#0) } 
  _module.__default.map__fg($ly, M#0) == _module.__default.map__fg($LZ, M#0));

// consequence axiom for _module.__default.map__fg
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.map__fg($ly, M#0) } 
    _module.__default.map__fg#canCall(M#0)
         || (3 != $FunctionContextHeight && $Is(M#0, Tclass._module.Stream(#$X)))
       ==> $Is(_module.__default.map__fg($ly, M#0), Tclass._module.Stream(#$X)));

function _module.__default.map__fg#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.map__fg
axiom (forall $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.map__fg#requires($ly, M#0) } 
  $Is(M#0, Tclass._module.Stream(#$X))
     ==> _module.__default.map__fg#requires($ly, M#0) == true);

// definition axiom for _module.__default.map__fg (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.map__fg($LS($ly), M#0) } 
    _module.__default.map__fg#canCall(M#0)
         || (3 != $FunctionContextHeight && $Is(M#0, Tclass._module.Stream(#$X)))
       ==> (!_module.Stream.Nil_q(M#0)
           ==> (var N#1 := _module.Stream.tail(M#0); 
            (var x#1 := _module.Stream.head(M#0); 
              _module.__default.g#canCall(x#1)
                 && _module.__default.f#canCall(_module.__default.g(x#1))
                 && _module.__default.map__fg#canCall(N#1))))
         && _module.__default.map__fg($LS($ly), M#0)
           == (if _module.Stream.Nil_q(M#0)
             then #_module.Stream.Nil()
             else (var N#0 := _module.Stream.tail(M#0); 
              (var x#0 := _module.Stream.head(M#0); 
                #_module.Stream.Cons(_module.__default.f(_module.__default.g(x#0)), 
                  _module.__default.map__fg($ly, N#0))))));

procedure CheckWellformed$$_module.__default.map__fg(M#0: DatatypeType where $Is(M#0, Tclass._module.Stream(#$X)));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.map__fg(M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var N#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: Box;
  var let#1#0#0: Box;
  var ##x#0: Box;
  var ##x#1: Box;
  var ##M#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function map_fg
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(36,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.map__fg($LS($LZ), M#0), Tclass._module.Stream(#$X));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (M#0 == #_module.Stream.Nil())
        {
            assume _module.__default.map__fg($LS($LZ), M#0) == Lit(#_module.Stream.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.map__fg($LS($LZ), M#0), Tclass._module.Stream(#$X));
        }
        else if (M#0 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, #$X);
            assume $Is(_mcc#1#0, Tclass._module.Stream(#$X));
            havoc N#Z#0;
            assume $Is(N#Z#0, Tclass._module.Stream(#$X));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(#$X));
            assume N#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $IsBox(x#Z#0, #$X);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, #$X);
            assume x#Z#0 == let#1#0#0;
            ##x#0 := x#Z#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#0, #$X, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.g#canCall(x#Z#0);
            ##x#1 := _module.__default.g(x#Z#0);
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#1, #$X, $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.f#canCall(_module.__default.g(x#Z#0));
            ##M#0 := N#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##M#0, Tclass._module.Stream(#$X), $Heap);
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.map__fg#canCall(N#Z#0);
            assume _module.__default.map__fg($LS($LZ), M#0)
               == #_module.Stream.Cons(_module.__default.f(_module.__default.g(x#Z#0)), 
                _module.__default.map__fg($LS($LZ), N#Z#0));
            assume _module.__default.g#canCall(x#Z#0)
               && _module.__default.f#canCall(_module.__default.g(x#Z#0))
               && _module.__default.map__fg#canCall(N#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.map__fg($LS($LZ), M#0), Tclass._module.Stream(#$X));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



procedure CheckWellformed$$_module.__default.Theorem0(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem0(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.map__fg($LS($LZ), M#0))
     && $IsA#_module.Stream(_module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)))
     && 
    _module.__default.map__fg#canCall(M#0)
     && 
    _module.__default.map__g#canCall(M#0)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.map__fg($LS($LS($LZ)), M#0), 
    _module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} CoCall$$_module.__default.Theorem0_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.map__fg#canCall(M#1)
     && 
    _module.__default.map__g#canCall(M#1)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#1));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.map__fg($LS($LZ), M#1), 
    _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} Impl$$_module.__default.Theorem0_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1))
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.map__fg#canCall(M#1)
     && 
    _module.__default.map__g#canCall(M#1)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#1));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.map__fg($LS($LS($LZ)), M#1))
       ==> _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.map__fg($LS($LS($LZ)), M#1))
       ==> _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))
         && 
        _module.Stream.head(_module.__default.map__fg($LS($LS($LZ)), M#1))
           == _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.map__fg($LS($LS($LZ)), M#1)), 
          _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1)))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.map__fg($LS($LS($LZ)), M#1))
           ==> _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1))))
         && (_module.Stream.Cons_q(_module.__default.map__fg($LS($LS($LZ)), M#1))
           ==> _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))
             && 
            _module.Stream.head(_module.__default.map__fg($LS($LS($LZ)), M#1))
               == _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))
             && $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.map__fg($LS($LS($LZ)), M#1)), 
              _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(#$X, 
        #$X, 
        $LS($LS($LZ)), 
        _module.__default.map__fg($LS($LZ), M#1), 
        _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1} Impl$$_module.__default.Theorem0_h(_k#0: Box, M#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var N#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var x#0: Box;
  var let#0_0_1#0#0: Box;
  var _k##0: Box;
  var M##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem0#, Impl$$_module.__default.Theorem0_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(46,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#M0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.map__fg($LS($LZ), $ih#M0#0), 
          _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), $ih#M0#0))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(48,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (M#1 == #_module.Stream.Nil())
        {
        }
        else if (M#1 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, #$X) && $IsAllocBox(_mcc#0#0, #$X, $Heap);
            assume $Is(_mcc#1#0, Tclass._module.Stream(#$X))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(#$X), $Heap);
            havoc N#0;
            assume $Is(N#0, Tclass._module.Stream(#$X))
               && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(#$X));
            assume N#0 == let#0_0_0#0#0;
            havoc x#0;
            assume $IsBox(x#0, #$X) && $IsAllocBox(x#0, #$X, $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0_0_1#0#0, #$X);
            assume x#0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(52,15)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := N#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem0_h(_k##0, M##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(52,17)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(46,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, M#2: DatatypeType :: 
          $Is(M#2, Tclass._module.Stream(#$X)) && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.map__fg($LS($LZ), M#2), 
              _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#2))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(46,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Theorem0__Alt(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem0__Alt(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.map__fg($LS($LZ), M#0))
     && $IsA#_module.Stream(_module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)))
     && 
    _module.__default.map__fg#canCall(M#0)
     && 
    _module.__default.map__g#canCall(M#0)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.map__fg($LS($LS($LZ)), M#0), 
    _module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} CoCall$$_module.__default.Theorem0__Alt_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.map__fg#canCall(M#1)
     && 
    _module.__default.map__g#canCall(M#1)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#1));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.map__fg($LS($LZ), M#1), 
    _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} Impl$$_module.__default.Theorem0__Alt_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1))
   returns ($_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.map__fg#canCall(M#1)
     && 
    _module.__default.map__g#canCall(M#1)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#1));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.map__fg($LS($LS($LZ)), M#1))
       ==> _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.map__fg($LS($LS($LZ)), M#1))
       ==> _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))
         && 
        _module.Stream.head(_module.__default.map__fg($LS($LS($LZ)), M#1))
           == _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.map__fg($LS($LS($LZ)), M#1)), 
          _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1)))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.map__fg($LS($LS($LZ)), M#1))
           ==> _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1))))
         && (_module.Stream.Cons_q(_module.__default.map__fg($LS($LS($LZ)), M#1))
           ==> _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))
             && 
            _module.Stream.head(_module.__default.map__fg($LS($LS($LZ)), M#1))
               == _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1)))
             && $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.map__fg($LS($LS($LZ)), M#1)), 
              _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#1))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(#$X, 
        #$X, 
        $LS($LS($LZ)), 
        _module.__default.map__fg($LS($LZ), M#1), 
        _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1} Impl$$_module.__default.Theorem0__Alt_h(_k#0: Box, M#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: Box;
  var M##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem0_Alt#, Impl$$_module.__default.Theorem0__Alt_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(55,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#M0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.map__fg($LS($LZ), $ih#M0#0), 
          _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), $ih#M0#0))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(57,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(58,3)
        assume true;
        if (_module.Stream.Cons_q(M#1))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(59,17)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assert _module.Stream.Cons_q(M#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := _module.Stream.tail(M#1);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem0__Alt_h(_k##0, M##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(59,24)"} true;
        }
        else
        {
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(55,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, M#2: DatatypeType :: 
          $Is(M#2, Tclass._module.Stream(#$X)) && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.map__fg($LS($LZ), M#2), 
              _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#2))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(55,15)"} true;
    }
}



procedure {:_induction M#0} CheckWellformed$$_module.__default.Theorem0__Par(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction M#0} Call$$_module.__default.Theorem0__Par(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.map__fg($LS($LZ), M#0))
     && $IsA#_module.Stream(_module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)))
     && 
    _module.__default.map__fg#canCall(M#0)
     && 
    _module.__default.map__g#canCall(M#0)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.map__fg($LS($LS($LZ)), M#0), 
    _module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction M#0} Impl$$_module.__default.Theorem0__Par(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0))
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.map__fg($LS($LZ), M#0))
     && $IsA#_module.Stream(_module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)))
     && 
    _module.__default.map__fg#canCall(M#0)
     && 
    _module.__default.map__g#canCall(M#0)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.map__fg($LS($LS($LZ)), M#0), 
    _module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction M#0} Impl$$_module.__default.Theorem0__Par(M#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var k#0: int;
  var k##0: int;
  var M##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem0_Par, Impl$$_module.__default.Theorem0__Par
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(64,0): initial state"} true;
    assume $IsA#_module.Stream(M#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#M0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X)) && Lit(true) && false
         ==> $Eq#_module.Stream(#$X, 
          #$X, 
          $LS($LS($LZ)), 
          _module.__default.map__fg($LS($LZ), $ih#M0#0), 
          _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), $ih#M0#0))));
    $_reverifyPost := false;
    // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(65,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc k#0;
        assume LitInt(0) <= k#0;
        assume true;
        assume true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(66,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        k##0 := k#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        M##0 := M#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Theorem0__Ind(k##0, M##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(66,22)"} true;
        assume false;
    }
    else
    {
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall k#1: int :: 
          LitInt(0) <= k#1 && Lit(true)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#FromNat(k#1), 
              $LS($LS($LZ)), 
              _module.__default.map__fg($LS($LZ), M#0), 
              _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0))));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(67,2)"} true;
}



procedure {:_induction k#0, M#0} CheckWellformed$$_module.__default.Theorem0__Ind(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction k#0, M#0} CheckWellformed$$_module.__default.Theorem0__Ind(k#0: int, M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##M#0: DatatypeType;
  var ##M#1: DatatypeType;
  var ##M#2: DatatypeType;

    // AddMethodImpl: Theorem0_Ind, CheckWellformed$$_module.__default.Theorem0__Ind
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(69,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(70,20): post-state"} true;
    ##M#0 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#0, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__fg#canCall(M#0);
    ##M#1 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#1, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__g#canCall(M#0);
    ##M#2 := _module.__default.map__g($LS($LZ), M#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#2, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
    assert 0 <= k#0;
    assume $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)));
}



procedure {:_induction k#0, M#0} Call$$_module.__default.Theorem0__Ind(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.map__fg#canCall(M#0)
     && 
    _module.__default.map__g#canCall(M#0)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    ORD#FromNat(k#0), 
    $LS($LS($LZ)), 
    _module.__default.map__fg($LS($LZ), M#0), 
    _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, M#0} Impl$$_module.__default.Theorem0__Ind(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0))
   returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.map__fg#canCall(M#0)
     && 
    _module.__default.map__g#canCall(M#0)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)))
     || (0 < k#0
       ==> 
      _module.Stream.Nil_q(_module.__default.map__fg($LS($LS($LZ)), M#0))
       ==> _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)))
     || (0 < k#0
       ==> 
      _module.Stream.Cons_q(_module.__default.map__fg($LS($LS($LZ)), M#0))
       ==> _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)))
         && 
        _module.Stream.head(_module.__default.map__fg($LS($LS($LZ)), M#0))
           == _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#FromNat(k#0 - 1), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.map__fg($LS($LS($LZ)), M#0)), 
          _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, M#0} Impl$$_module.__default.Theorem0__Ind(k#0: int, M#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0_0: Box;
  var _mcc#1#0_0_0: DatatypeType;
  var N#0_0_0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var x#0_0_0: Box;
  var let#0_0_1#0#0: Box;
  var k##0_0_0: int;
  var M##0_0_0: DatatypeType;

    // AddMethodImpl: Theorem0_Ind, Impl$$_module.__default.Theorem0__Ind
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(71,0): initial state"} true;
    assume $IsA#_module.Stream(M#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, $ih#M0#0: DatatypeType :: 
      LitInt(0) <= $ih#k0#0
           && $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#FromNat($ih#k0#0), 
          $LS($LS($LZ)), 
          _module.__default.map__fg($LS($LZ), $ih#M0#0), 
          _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), $ih#M0#0))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(72,3)
    assume true;
    if (k#0 != 0)
    {
        assume true;
        havoc _mcc#0#0_0_0, _mcc#1#0_0_0;
        if (M#0 == #_module.Stream.Nil())
        {
        }
        else if (M#0 == #_module.Stream.Cons(_mcc#0#0_0_0, _mcc#1#0_0_0))
        {
            assume $IsBox(_mcc#0#0_0_0, #$X);
            assume $Is(_mcc#1#0_0_0, Tclass._module.Stream(#$X));
            havoc N#0_0_0;
            assume $Is(N#0_0_0, Tclass._module.Stream(#$X))
               && $IsAlloc(N#0_0_0, Tclass._module.Stream(#$X), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0_0_0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(#$X));
            assume N#0_0_0 == let#0_0_0#0#0;
            havoc x#0_0_0;
            assume $IsBox(x#0_0_0, #$X) && $IsAllocBox(x#0_0_0, #$X, $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0_0_0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0_0_1#0#0, #$X);
            assume x#0_0_0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(76,21)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(k#0 - 1, Tclass._System.nat());
            k##0_0_0 := k#0 - 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0_0_0 := N#0_0_0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= k#0 || k##0_0_0 == k#0;
            assert k##0_0_0 < k#0;
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Theorem0__Ind(k##0_0_0, M##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(76,28)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
    }
}



procedure {:_induction k#0, M#0} CheckWellformed$$_module.__default.Theorem0__AutoInd(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction k#0, M#0} CheckWellformed$$_module.__default.Theorem0__AutoInd(k#0: int, M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##M#0: DatatypeType;
  var ##M#1: DatatypeType;
  var ##M#2: DatatypeType;

    // AddMethodImpl: Theorem0_AutoInd, CheckWellformed$$_module.__default.Theorem0__AutoInd
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(80,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(81,20): post-state"} true;
    ##M#0 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#0, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__fg#canCall(M#0);
    ##M#1 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#1, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__g#canCall(M#0);
    ##M#2 := _module.__default.map__g($LS($LZ), M#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#2, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
    assert 0 <= k#0;
    assume $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)));
}



procedure {:_induction k#0, M#0} Call$$_module.__default.Theorem0__AutoInd(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.map__fg#canCall(M#0)
     && 
    _module.__default.map__g#canCall(M#0)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    ORD#FromNat(k#0), 
    $LS($LS($LZ)), 
    _module.__default.map__fg($LS($LZ), M#0), 
    _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, M#0} Impl$$_module.__default.Theorem0__AutoInd(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.map__fg#canCall(M#0)
     && 
    _module.__default.map__g#canCall(M#0)
     && _module.__default.map__f#canCall(_module.__default.map__g($LS($LZ), M#0));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)))
     || (0 < k#0
       ==> 
      _module.Stream.Nil_q(_module.__default.map__fg($LS($LS($LZ)), M#0))
       ==> _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__fg($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), M#0)))
     || (0 < k#0
       ==> 
      _module.Stream.Cons_q(_module.__default.map__fg($LS($LS($LZ)), M#0))
       ==> _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)))
         && 
        _module.Stream.head(_module.__default.map__fg($LS($LS($LZ)), M#0))
           == _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#FromNat(k#0 - 1), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.map__fg($LS($LS($LZ)), M#0)), 
          _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.map__g($LS($LS($LZ)), M#0)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, M#0} Impl$$_module.__default.Theorem0__AutoInd(k#0: int, M#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem0_AutoInd, Impl$$_module.__default.Theorem0__AutoInd
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(82,0): initial state"} true;
    assume $IsA#_module.Stream(M#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, $ih#M0#0: DatatypeType :: 
      LitInt(0) <= $ih#k0#0
           && $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#FromNat($ih#k0#0), 
          $LS($LS($LZ)), 
          _module.__default.map__fg($LS($LZ), $ih#M0#0), 
          _module.__default.map__f($LS($LZ), _module.__default.map__g($LS($LZ), $ih#M0#0))));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Theorem1(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem1(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)))
     && $IsA#_module.Stream(_module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)))
     && 
    _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0))
     && 
    _module.__default.map__f#canCall(M#0)
     && _module.__default.map__f#canCall(N#0)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)), 
    _module.__default.append(#$X, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LS($LZ)), M#0), 
      _module.__default.map__f($LS($LS($LZ)), N#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1, N#1} CoCall$$_module.__default.Theorem1_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1), 
    N#1: DatatypeType
       where $Is(N#1, Tclass._module.Stream(#$X))
         && $IsAlloc(N#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#1, N#1)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#1, N#1))
     && 
    _module.__default.map__f#canCall(M#1)
     && _module.__default.map__f#canCall(N#1)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), N#1));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
    _module.__default.append(#$X, 
      $LS($LZ), 
      _module.__default.map__f($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), N#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1, N#1} Impl$$_module.__default.Theorem1_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1), 
    N#1: DatatypeType
       where $Is(N#1, Tclass._module.Stream(#$X))
         && $IsAlloc(N#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#1))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#1, N#1)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#1, N#1))
     && 
    _module.__default.map__f#canCall(M#1)
     && _module.__default.map__f#canCall(N#1)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), N#1));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#1), 
        _module.__default.map__f($LS($LZ), N#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
       ==> _module.Stream.Nil_q(_module.__default.append(#$X, 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LS($LZ)), M#1), 
          _module.__default.map__f($LS($LS($LZ)), N#1))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#1), 
        _module.__default.map__f($LS($LZ), N#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
       ==> _module.Stream.Cons_q(_module.__default.append(#$X, 
            $LS($LS($LZ)), 
            _module.__default.map__f($LS($LS($LZ)), M#1), 
            _module.__default.map__f($LS($LS($LZ)), N#1)))
         && 
        _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
           == _module.Stream.head(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#1), 
              _module.__default.map__f($LS($LS($LZ)), N#1)))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1))), 
          _module.Stream.tail(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#1), 
              _module.__default.map__f($LS($LS($LZ)), N#1)))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#1), 
        _module.__default.map__f($LS($LZ), N#1)))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
           ==> _module.Stream.Nil_q(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#1), 
              _module.__default.map__f($LS($LS($LZ)), N#1))))
         && (_module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
           ==> _module.Stream.Cons_q(_module.__default.append(#$X, 
                $LS($LS($LZ)), 
                _module.__default.map__f($LS($LS($LZ)), M#1), 
                _module.__default.map__f($LS($LS($LZ)), N#1)))
             && 
            _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
               == _module.Stream.head(_module.__default.append(#$X, 
                  $LS($LS($LZ)), 
                  _module.__default.map__f($LS($LS($LZ)), M#1), 
                  _module.__default.map__f($LS($LS($LZ)), N#1)))
             && $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1))), 
              _module.Stream.tail(_module.__default.append(#$X, 
                  $LS($LS($LZ)), 
                  _module.__default.map__f($LS($LS($LZ)), M#1), 
                  _module.__default.map__f($LS($LS($LZ)), N#1))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(#$X, 
        #$X, 
        $LS($LS($LZ)), 
        _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
        _module.__default.append(#$X, 
          $LS($LZ), 
          _module.__default.map__f($LS($LZ), M#1), 
          _module.__default.map__f($LS($LZ), N#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1, N#1} Impl$$_module.__default.Theorem1_h(_k#0: Box, M#1: DatatypeType, N#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var M'#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var x#0: Box;
  var let#0_0_1#0#0: Box;
  var _k##0: Box;
  var M##0: DatatypeType;
  var N##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem1#, Impl$$_module.__default.Theorem1_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(86,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    assume $IsA#_module.Stream(N#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#M0#0: DatatypeType, $ih#N0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && $Is($ih#N0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), $ih#M0#0, $ih#N0#0)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            _module.__default.map__f($LS($LZ), $ih#M0#0), 
            _module.__default.map__f($LS($LZ), $ih#N0#0))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(88,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (M#1 == #_module.Stream.Nil())
        {
        }
        else if (M#1 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, #$X) && $IsAllocBox(_mcc#0#0, #$X, $Heap);
            assume $Is(_mcc#1#0, Tclass._module.Stream(#$X))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(#$X), $Heap);
            havoc M'#0;
            assume $Is(M'#0, Tclass._module.Stream(#$X))
               && $IsAlloc(M'#0, Tclass._module.Stream(#$X), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(#$X));
            assume M'#0 == let#0_0_0#0#0;
            havoc x#0;
            assume $IsBox(x#0, #$X) && $IsAllocBox(x#0, #$X, $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0_0_1#0#0, #$X);
            assume x#0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(92,15)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := M'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            N##0 := N#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem1_h(_k##0, M##0, N##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(92,21)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(86,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, M#2: DatatypeType, N#2: DatatypeType :: 
          $Is(M#2, Tclass._module.Stream(#$X))
               && $Is(N#2, Tclass._module.Stream(#$X))
               && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#2, N#2)), 
              _module.__default.append(#$X, 
                $LS($LZ), 
                _module.__default.map__f($LS($LZ), M#2), 
                _module.__default.map__f($LS($LZ), N#2))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(86,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Theorem1__Alt(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem1__Alt(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)))
     && $IsA#_module.Stream(_module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)))
     && 
    _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0))
     && 
    _module.__default.map__f#canCall(M#0)
     && _module.__default.map__f#canCall(N#0)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)), 
    _module.__default.append(#$X, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LS($LZ)), M#0), 
      _module.__default.map__f($LS($LS($LZ)), N#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1, N#1} CoCall$$_module.__default.Theorem1__Alt_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1), 
    N#1: DatatypeType
       where $Is(N#1, Tclass._module.Stream(#$X))
         && $IsAlloc(N#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#1, N#1)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#1, N#1))
     && 
    _module.__default.map__f#canCall(M#1)
     && _module.__default.map__f#canCall(N#1)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), N#1));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
    _module.__default.append(#$X, 
      $LS($LZ), 
      _module.__default.map__f($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), N#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1, N#1} Impl$$_module.__default.Theorem1__Alt_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1), 
    N#1: DatatypeType
       where $Is(N#1, Tclass._module.Stream(#$X))
         && $IsAlloc(N#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#1))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#1, N#1)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#1, N#1))
     && 
    _module.__default.map__f#canCall(M#1)
     && _module.__default.map__f#canCall(N#1)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#1), 
      _module.__default.map__f($LS($LZ), N#1));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#1), 
        _module.__default.map__f($LS($LZ), N#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
       ==> _module.Stream.Nil_q(_module.__default.append(#$X, 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LS($LZ)), M#1), 
          _module.__default.map__f($LS($LS($LZ)), N#1))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#1), 
        _module.__default.map__f($LS($LZ), N#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
       ==> _module.Stream.Cons_q(_module.__default.append(#$X, 
            $LS($LS($LZ)), 
            _module.__default.map__f($LS($LS($LZ)), M#1), 
            _module.__default.map__f($LS($LS($LZ)), N#1)))
         && 
        _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
           == _module.Stream.head(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#1), 
              _module.__default.map__f($LS($LS($LZ)), N#1)))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1))), 
          _module.Stream.tail(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#1), 
              _module.__default.map__f($LS($LS($LZ)), N#1)))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#1), 
        _module.__default.map__f($LS($LZ), N#1)))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
           ==> _module.Stream.Nil_q(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#1), 
              _module.__default.map__f($LS($LS($LZ)), N#1))))
         && (_module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
           ==> _module.Stream.Cons_q(_module.__default.append(#$X, 
                $LS($LS($LZ)), 
                _module.__default.map__f($LS($LS($LZ)), M#1), 
                _module.__default.map__f($LS($LS($LZ)), N#1)))
             && 
            _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1)))
               == _module.Stream.head(_module.__default.append(#$X, 
                  $LS($LS($LZ)), 
                  _module.__default.map__f($LS($LS($LZ)), M#1), 
                  _module.__default.map__f($LS($LS($LZ)), N#1)))
             && $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1))), 
              _module.Stream.tail(_module.__default.append(#$X, 
                  $LS($LS($LZ)), 
                  _module.__default.map__f($LS($LS($LZ)), M#1), 
                  _module.__default.map__f($LS($LS($LZ)), N#1))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(#$X, 
        #$X, 
        $LS($LS($LZ)), 
        _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1)), 
        _module.__default.append(#$X, 
          $LS($LZ), 
          _module.__default.map__f($LS($LZ), M#1), 
          _module.__default.map__f($LS($LZ), N#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1, N#1} Impl$$_module.__default.Theorem1__Alt_h(_k#0: Box, M#1: DatatypeType, N#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: Box;
  var M##0: DatatypeType;
  var N##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem1_Alt#, Impl$$_module.__default.Theorem1__Alt_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(95,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    assume $IsA#_module.Stream(N#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#M0#0: DatatypeType, $ih#N0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && $Is($ih#N0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), $ih#M0#0, $ih#N0#0)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            _module.__default.map__f($LS($LZ), $ih#M0#0), 
            _module.__default.map__f($LS($LZ), $ih#N0#0))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(97,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(98,3)
        assume true;
        if (_module.Stream.Cons_q(M#1))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(99,17)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assert _module.Stream.Cons_q(M#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := _module.Stream.tail(M#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            N##0 := N#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem1__Alt_h(_k##0, M##0, N##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(99,27)"} true;
        }
        else
        {
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(95,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, M#2: DatatypeType, N#2: DatatypeType :: 
          $Is(M#2, Tclass._module.Stream(#$X))
               && $Is(N#2, Tclass._module.Stream(#$X))
               && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#2, N#2)), 
              _module.__default.append(#$X, 
                $LS($LZ), 
                _module.__default.map__f($LS($LZ), M#2), 
                _module.__default.map__f($LS($LZ), N#2))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(95,15)"} true;
    }
}



procedure {:_induction M#0, N#0} CheckWellformed$$_module.__default.Theorem1__Par(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction M#0, N#0} Call$$_module.__default.Theorem1__Par(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)))
     && $IsA#_module.Stream(_module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)))
     && 
    _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0))
     && 
    _module.__default.map__f#canCall(M#0)
     && _module.__default.map__f#canCall(N#0)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)), 
    _module.__default.append(#$X, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LS($LZ)), M#0), 
      _module.__default.map__f($LS($LS($LZ)), N#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction M#0, N#0} Impl$$_module.__default.Theorem1__Par(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0))
   returns ($_reverifyPost: bool);
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)))
     && $IsA#_module.Stream(_module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)))
     && 
    _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0))
     && 
    _module.__default.map__f#canCall(M#0)
     && _module.__default.map__f#canCall(N#0)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)), 
    _module.__default.append(#$X, 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LS($LZ)), M#0), 
      _module.__default.map__f($LS($LS($LZ)), N#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction M#0, N#0} Impl$$_module.__default.Theorem1__Par(M#0: DatatypeType, N#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var k#0: int;
  var k##0: int;
  var M##0: DatatypeType;
  var N##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem1_Par, Impl$$_module.__default.Theorem1__Par
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(104,0): initial state"} true;
    assume $IsA#_module.Stream(M#0);
    assume $IsA#_module.Stream(N#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#M0#0: DatatypeType, $ih#N0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && $Is($ih#N0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && false
         ==> $Eq#_module.Stream(#$X, 
          #$X, 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), $ih#M0#0, $ih#N0#0)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            _module.__default.map__f($LS($LZ), $ih#M0#0), 
            _module.__default.map__f($LS($LZ), $ih#N0#0))));
    $_reverifyPost := false;
    // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(105,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc k#0;
        assume LitInt(0) <= k#0;
        assume true;
        assume true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(106,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        k##0 := k#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        M##0 := M#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        N##0 := N#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Theorem1__Ind(k##0, M##0, N##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(106,25)"} true;
        assume false;
    }
    else
    {
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall k#1: int :: 
          LitInt(0) <= k#1 && Lit(true)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#FromNat(k#1), 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
              _module.__default.append(#$X, 
                $LS($LZ), 
                _module.__default.map__f($LS($LZ), M#0), 
                _module.__default.map__f($LS($LZ), N#0))));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(107,2)"} true;
}



procedure {:_induction k#0, M#0, N#0} CheckWellformed$$_module.__default.Theorem1__Ind(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction k#0, M#0, N#0} CheckWellformed$$_module.__default.Theorem1__Ind(k#0: int, M#0: DatatypeType, N#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##M#0: DatatypeType;
  var ##N#0: DatatypeType;
  var ##M#1: DatatypeType;
  var ##M#2: DatatypeType;
  var ##M#3: DatatypeType;
  var ##M#4: DatatypeType;
  var ##N#1: DatatypeType;

    // AddMethodImpl: Theorem1_Ind, CheckWellformed$$_module.__default.Theorem1__Ind
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(109,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(110,30): post-state"} true;
    ##M#0 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#0, Tclass._module.Stream(#$X), $Heap);
    ##N#0 := N#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##N#0, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.append#canCall(#$X, M#0, N#0);
    ##M#1 := _module.__default.append(#$X, $LS($LZ), M#0, N#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#1, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0));
    ##M#2 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#2, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__f#canCall(M#0);
    ##M#3 := N#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#3, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__f#canCall(N#0);
    ##M#4 := _module.__default.map__f($LS($LZ), M#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#4, Tclass._module.Stream(#$X), $Heap);
    ##N#1 := _module.__default.map__f($LS($LZ), N#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##N#1, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
    assert 0 <= k#0;
    assume $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)));
}



procedure {:_induction k#0, M#0, N#0} Call$$_module.__default.Theorem1__Ind(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0))
     && 
    _module.__default.map__f#canCall(M#0)
     && _module.__default.map__f#canCall(N#0)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    ORD#FromNat(k#0), 
    $LS($LS($LZ)), 
    _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
    _module.__default.append(#$X, 
      $LS($LZ), 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, M#0, N#0} Impl$$_module.__default.Theorem1__Ind(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0))
   returns ($_reverifyPost: bool);
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0))
     && 
    _module.__default.map__f#canCall(M#0)
     && _module.__default.map__f#canCall(N#0)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)))
     || (0 < k#0
       ==> 
      _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)))
       ==> _module.Stream.Nil_q(_module.__default.append(#$X, 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LS($LZ)), M#0), 
          _module.__default.map__f($LS($LS($LZ)), N#0))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)))
     || (0 < k#0
       ==> 
      _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)))
       ==> _module.Stream.Cons_q(_module.__default.append(#$X, 
            $LS($LS($LZ)), 
            _module.__default.map__f($LS($LS($LZ)), M#0), 
            _module.__default.map__f($LS($LS($LZ)), N#0)))
         && 
        _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)))
           == _module.Stream.head(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#0), 
              _module.__default.map__f($LS($LS($LZ)), N#0)))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#FromNat(k#0 - 1), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0))), 
          _module.Stream.tail(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#0), 
              _module.__default.map__f($LS($LS($LZ)), N#0)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, M#0, N#0} Impl$$_module.__default.Theorem1__Ind(k#0: int, M#0: DatatypeType, N#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: Box;
  var _mcc#1#0_0: DatatypeType;
  var M'#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var x#0_0: Box;
  var let#0_1#0#0: Box;
  var k##0_0_0: int;
  var M##0_0_0: DatatypeType;
  var N##0_0_0: DatatypeType;

    // AddMethodImpl: Theorem1_Ind, Impl$$_module.__default.Theorem1__Ind
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(111,0): initial state"} true;
    assume $IsA#_module.Stream(M#0);
    assume $IsA#_module.Stream(N#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, $ih#M0#0: DatatypeType, $ih#N0#0: DatatypeType :: 
      LitInt(0) <= $ih#k0#0
           && $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && $Is($ih#N0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#FromNat($ih#k0#0), 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), $ih#M0#0, $ih#N0#0)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            _module.__default.map__f($LS($LZ), $ih#M0#0), 
            _module.__default.map__f($LS($LZ), $ih#N0#0))));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (M#0 == #_module.Stream.Nil())
    {
    }
    else if (M#0 == #_module.Stream.Cons(_mcc#0#0_0, _mcc#1#0_0))
    {
        assume $IsBox(_mcc#0#0_0, #$X);
        assume $Is(_mcc#1#0_0, Tclass._module.Stream(#$X));
        havoc M'#0_0;
        assume $Is(M'#0_0, Tclass._module.Stream(#$X))
           && $IsAlloc(M'#0_0, Tclass._module.Stream(#$X), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Stream(#$X));
        assume M'#0_0 == let#0_0#0#0;
        havoc x#0_0;
        assume $IsBox(x#0_0, #$X) && $IsAllocBox(x#0_0, #$X, $Heap);
        assume let#0_1#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $IsBox(let#0_1#0#0, #$X);
        assume x#0_0 == let#0_1#0#0;
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(116,7)
        assume true;
        if (k#0 != 0)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(117,21)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(k#0 - 1, Tclass._System.nat());
            k##0_0_0 := k#0 - 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0_0_0 := M'#0_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            N##0_0_0 := N#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= k#0 || k##0_0_0 == k#0;
            assert k##0_0_0 < k#0;
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Theorem1__Ind(k##0_0_0, M##0_0_0, N##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(117,32)"} true;
        }
        else
        {
        }
    }
    else
    {
        assume false;
    }
}



procedure {:_induction k#0, M#0, N#0} CheckWellformed$$_module.__default.Theorem1__AutoInd(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction k#0, M#0, N#0} CheckWellformed$$_module.__default.Theorem1__AutoInd(k#0: int, M#0: DatatypeType, N#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##M#0: DatatypeType;
  var ##N#0: DatatypeType;
  var ##M#1: DatatypeType;
  var ##M#2: DatatypeType;
  var ##M#3: DatatypeType;
  var ##M#4: DatatypeType;
  var ##N#1: DatatypeType;

    // AddMethodImpl: Theorem1_AutoInd, CheckWellformed$$_module.__default.Theorem1__AutoInd
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(121,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(122,30): post-state"} true;
    ##M#0 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#0, Tclass._module.Stream(#$X), $Heap);
    ##N#0 := N#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##N#0, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.append#canCall(#$X, M#0, N#0);
    ##M#1 := _module.__default.append(#$X, $LS($LZ), M#0, N#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#1, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0));
    ##M#2 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#2, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__f#canCall(M#0);
    ##M#3 := N#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#3, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.map__f#canCall(N#0);
    ##M#4 := _module.__default.map__f($LS($LZ), M#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#4, Tclass._module.Stream(#$X), $Heap);
    ##N#1 := _module.__default.map__f($LS($LZ), N#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##N#1, Tclass._module.Stream(#$X), $Heap);
    assume _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
    assert 0 <= k#0;
    assume $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)));
}



procedure {:_induction k#0, M#0, N#0} Call$$_module.__default.Theorem1__AutoInd(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0))
     && 
    _module.__default.map__f#canCall(M#0)
     && _module.__default.map__f#canCall(N#0)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    ORD#FromNat(k#0), 
    $LS($LS($LZ)), 
    _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
    _module.__default.append(#$X, 
      $LS($LZ), 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, M#0, N#0} Impl$$_module.__default.Theorem1__AutoInd(k#0: int where LitInt(0) <= k#0, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0))
   returns ($_reverifyPost: bool);
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.map__f#canCall(_module.__default.append(#$X, $LS($LZ), M#0, N#0))
     && 
    _module.__default.map__f#canCall(M#0)
     && _module.__default.map__f#canCall(N#0)
     && _module.__default.append#canCall(#$X, 
      _module.__default.map__f($LS($LZ), M#0), 
      _module.__default.map__f($LS($LZ), N#0));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)))
     || (0 < k#0
       ==> 
      _module.Stream.Nil_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)))
       ==> _module.Stream.Nil_q(_module.__default.append(#$X, 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LS($LZ)), M#0), 
          _module.__default.map__f($LS($LS($LZ)), N#0))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0)), 
      _module.__default.append(#$X, 
        $LS($LZ), 
        _module.__default.map__f($LS($LZ), M#0), 
        _module.__default.map__f($LS($LZ), N#0)))
     || (0 < k#0
       ==> 
      _module.Stream.Cons_q(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)))
       ==> _module.Stream.Cons_q(_module.__default.append(#$X, 
            $LS($LS($LZ)), 
            _module.__default.map__f($LS($LS($LZ)), M#0), 
            _module.__default.map__f($LS($LS($LZ)), N#0)))
         && 
        _module.Stream.head(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0)))
           == _module.Stream.head(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#0), 
              _module.__default.map__f($LS($LS($LZ)), N#0)))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#FromNat(k#0 - 1), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.map__f($LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0))), 
          _module.Stream.tail(_module.__default.append(#$X, 
              $LS($LS($LZ)), 
              _module.__default.map__f($LS($LS($LZ)), M#0), 
              _module.__default.map__f($LS($LS($LZ)), N#0)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, M#0, N#0} Impl$$_module.__default.Theorem1__AutoInd(k#0: int, M#0: DatatypeType, N#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem1_AutoInd, Impl$$_module.__default.Theorem1__AutoInd
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(123,0): initial state"} true;
    assume $IsA#_module.Stream(M#0);
    assume $IsA#_module.Stream(N#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, $ih#M0#0: DatatypeType, $ih#N0#0: DatatypeType :: 
      LitInt(0) <= $ih#k0#0
           && $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && $Is($ih#N0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && 
          0 <= $ih#k0#0
           && $ih#k0#0 < k#0
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#FromNat($ih#k0#0), 
          $LS($LS($LZ)), 
          _module.__default.map__f($LS($LZ), _module.__default.append(#$X, $LS($LZ), $ih#M0#0, $ih#N0#0)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            _module.__default.map__f($LS($LZ), $ih#M0#0), 
            _module.__default.map__f($LS($LZ), $ih#N0#0))));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Theorem1__AutoForall();
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem1__AutoForall();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Theorem1__AutoForall() returns ($_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction M#0} CheckWellformed$$_module.__default.Theorem2(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction M#0} Call$$_module.__default.Theorem2(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.append(#$X, $LS($LZ), Lit(#_module.Stream.Nil()), M#0))
     && $IsA#_module.Stream(M#0)
     && _module.__default.append#canCall(#$X, Lit(#_module.Stream.Nil()), M#0);
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LS($LZ)), Lit(#_module.Stream.Nil()), M#0), 
    M#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction M#0} Impl$$_module.__default.Theorem2(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0))
   returns ($_reverifyPost: bool);
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.append(#$X, $LS($LZ), Lit(#_module.Stream.Nil()), M#0))
     && $IsA#_module.Stream(M#0)
     && _module.__default.append#canCall(#$X, Lit(#_module.Stream.Nil()), M#0);
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LS($LZ)), Lit(#_module.Stream.Nil()), M#0), 
    M#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction M#0} Impl$$_module.__default.Theorem2(M#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem2, Impl$$_module.__default.Theorem2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(133,0): initial state"} true;
    assume $IsA#_module.Stream(M#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#M0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X)) && Lit(true) && false
         ==> $Eq#_module.Stream(#$X, 
          #$X, 
          $LS($LS($LZ)), 
          _module.__default.append(#$X, $LS($LZ), Lit(#_module.Stream.Nil()), $ih#M0#0), 
          $ih#M0#0));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.Theorem3(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem3(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.append(#$X, $LS($LZ), M#0, Lit(#_module.Stream.Nil())))
     && $IsA#_module.Stream(M#0)
     && _module.__default.append#canCall(#$X, M#0, Lit(#_module.Stream.Nil()));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LS($LZ)), M#0, Lit(#_module.Stream.Nil())), 
    M#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} CoCall$$_module.__default.Theorem3_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#1, Lit(#_module.Stream.Nil()));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
    M#1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} Impl$$_module.__default.Theorem3_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1))
   returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#1, Lit(#_module.Stream.Nil()));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
      M#1)
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
       ==> _module.Stream.Nil_q(M#1));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
      M#1)
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
       ==> _module.Stream.Cons_q(M#1)
         && 
        _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
           == _module.Stream.head(M#1)
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil()))), 
          _module.Stream.tail(M#1)));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
      M#1)
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
           ==> _module.Stream.Nil_q(M#1))
         && (_module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
           ==> _module.Stream.Cons_q(M#1)
             && 
            _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
               == _module.Stream.head(M#1)
             && $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil()))), 
              _module.Stream.tail(M#1))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(#$X, 
        #$X, 
        $LS($LS($LZ)), 
        _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
        M#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1} Impl$$_module.__default.Theorem3_h(_k#0: Box, M#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var N#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var x#0: Box;
  var let#0_0_1#0#0: Box;
  var _k##0: Box;
  var M##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem3#, Impl$$_module.__default.Theorem3_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(138,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#M0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.append(#$X, $LS($LZ), $ih#M0#0, Lit(#_module.Stream.Nil())), 
          $ih#M0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(140,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (M#1 == #_module.Stream.Nil())
        {
        }
        else if (M#1 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, #$X) && $IsAllocBox(_mcc#0#0, #$X, $Heap);
            assume $Is(_mcc#1#0, Tclass._module.Stream(#$X))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(#$X), $Heap);
            havoc N#0;
            assume $Is(N#0, Tclass._module.Stream(#$X))
               && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(#$X));
            assume N#0 == let#0_0_0#0#0;
            havoc x#0;
            assume $IsBox(x#0, #$X) && $IsAllocBox(x#0, #$X, $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0_0_1#0#0, #$X);
            assume x#0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(144,15)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := N#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem3_h(_k##0, M##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(144,17)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(138,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, M#2: DatatypeType :: 
          $Is(M#2, Tclass._module.Stream(#$X)) && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.append(#$X, $LS($LZ), M#2, Lit(#_module.Stream.Nil())), 
              M#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(138,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Theorem3__Alt(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem3__Alt(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.append(#$X, $LS($LZ), M#0, Lit(#_module.Stream.Nil())))
     && $IsA#_module.Stream(M#0)
     && _module.__default.append#canCall(#$X, M#0, Lit(#_module.Stream.Nil()));
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LS($LZ)), M#0, Lit(#_module.Stream.Nil())), 
    M#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} CoCall$$_module.__default.Theorem3__Alt_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#1, Lit(#_module.Stream.Nil()));
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
    M#1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} Impl$$_module.__default.Theorem3__Alt_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1))
   returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, M#1, Lit(#_module.Stream.Nil()));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
      M#1)
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
       ==> _module.Stream.Nil_q(M#1));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
      M#1)
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
       ==> _module.Stream.Cons_q(M#1)
         && 
        _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
           == _module.Stream.head(M#1)
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil()))), 
          _module.Stream.tail(M#1)));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
      M#1)
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
           ==> _module.Stream.Nil_q(M#1))
         && (_module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
           ==> _module.Stream.Cons_q(M#1)
             && 
            _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil())))
               == _module.Stream.head(M#1)
             && $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), M#1, Lit(#_module.Stream.Nil()))), 
              _module.Stream.tail(M#1))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(#$X, 
        #$X, 
        $LS($LS($LZ)), 
        _module.__default.append(#$X, $LS($LZ), M#1, Lit(#_module.Stream.Nil())), 
        M#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1} Impl$$_module.__default.Theorem3__Alt_h(_k#0: Box, M#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: Box;
  var M##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem3_Alt#, Impl$$_module.__default.Theorem3__Alt_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(147,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#M0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.append(#$X, $LS($LZ), $ih#M0#0, Lit(#_module.Stream.Nil())), 
          $ih#M0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(149,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(150,3)
        assume true;
        if (_module.Stream.Cons_q(M#1))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(151,17)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assert _module.Stream.Cons_q(M#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := _module.Stream.tail(M#1);
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem3__Alt_h(_k##0, M##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(151,24)"} true;
        }
        else
        {
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(147,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, M#2: DatatypeType :: 
          $Is(M#2, Tclass._module.Stream(#$X)) && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.append(#$X, $LS($LZ), M#2, Lit(#_module.Stream.Nil())), 
              M#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(147,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Theorem4(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0), 
    P#0: DatatypeType
       where $Is(P#0, Tclass._module.Stream(#$X))
         && $IsAlloc(P#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(P#0));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem4(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0), 
    P#0: DatatypeType
       where $Is(P#0, Tclass._module.Stream(#$X))
         && $IsAlloc(P#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(P#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.append(#$X, $LS($LZ), M#0, _module.__default.append(#$X, $LS($LZ), N#0, P#0)))
     && $IsA#_module.Stream(_module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0), P#0))
     && 
    _module.__default.append#canCall(#$X, N#0, P#0)
     && _module.__default.append#canCall(#$X, M#0, _module.__default.append(#$X, $LS($LZ), N#0, P#0))
     && 
    _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.append#canCall(#$X, _module.__default.append(#$X, $LS($LZ), M#0, N#0), P#0);
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LS($LZ)), M#0, _module.__default.append(#$X, $LS($LS($LZ)), N#0, P#0)), 
    _module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0), P#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1, N#1, P#1} CoCall$$_module.__default.Theorem4_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1), 
    N#1: DatatypeType
       where $Is(N#1, Tclass._module.Stream(#$X))
         && $IsAlloc(N#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#1), 
    P#1: DatatypeType
       where $Is(P#1, Tclass._module.Stream(#$X))
         && $IsAlloc(P#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(P#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, N#1, P#1)
     && _module.__default.append#canCall(#$X, M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1))
     && 
    _module.__default.append#canCall(#$X, M#1, N#1)
     && _module.__default.append#canCall(#$X, _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1);
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
    _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1, N#1, P#1} Impl$$_module.__default.Theorem4_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1), 
    N#1: DatatypeType
       where $Is(N#1, Tclass._module.Stream(#$X))
         && $IsAlloc(N#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#1), 
    P#1: DatatypeType
       where $Is(P#1, Tclass._module.Stream(#$X))
         && $IsAlloc(P#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(P#1))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, N#1, P#1)
     && _module.__default.append#canCall(#$X, M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1))
     && 
    _module.__default.append#canCall(#$X, M#1, N#1)
     && _module.__default.append#canCall(#$X, _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1);
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
      _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
       ==> _module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1)));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
      _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
       ==> _module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))
         && 
        _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
           == _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1))), 
          _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
      _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
           ==> _module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1)))
         && (_module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
           ==> _module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))
             && 
            _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
               == _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))
             && $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1))), 
              _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1)))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(#$X, 
        #$X, 
        $LS($LS($LZ)), 
        _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
        _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1, N#1, P#1} Impl$$_module.__default.Theorem4_h(_k#0: Box, M#1: DatatypeType, N#1: DatatypeType, P#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var M'#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var x#0: Box;
  var let#0_0_1#0#0: Box;
  var _k##0: Box;
  var M##0: DatatypeType;
  var N##0: DatatypeType;
  var P##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem4#, Impl$$_module.__default.Theorem4_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(156,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    assume $IsA#_module.Stream(N#1);
    assume $IsA#_module.Stream(P#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#M0#0: DatatypeType, 
        $ih#N0#0: DatatypeType, 
        $ih#P0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && $Is($ih#N0#0, Tclass._module.Stream(#$X))
           && $Is($ih#P0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            $ih#M0#0, 
            _module.__default.append(#$X, $LS($LZ), $ih#N0#0, $ih#P0#0)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            _module.__default.append(#$X, $LS($LZ), $ih#M0#0, $ih#N0#0), 
            $ih#P0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(158,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (M#1 == #_module.Stream.Nil())
        {
        }
        else if (M#1 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, #$X) && $IsAllocBox(_mcc#0#0, #$X, $Heap);
            assume $Is(_mcc#1#0, Tclass._module.Stream(#$X))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(#$X), $Heap);
            havoc M'#0;
            assume $Is(M'#0, Tclass._module.Stream(#$X))
               && $IsAlloc(M'#0, Tclass._module.Stream(#$X), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(#$X));
            assume M'#0 == let#0_0_0#0#0;
            havoc x#0;
            assume $IsBox(x#0, #$X) && $IsAllocBox(x#0, #$X, $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0_0_1#0#0, #$X);
            assume x#0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(162,15)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := M'#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            N##0 := N#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##0 := P#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem4_h(_k##0, M##0, N##0, P##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(162,24)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(156,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, M#2: DatatypeType, N#2: DatatypeType, P#2: DatatypeType :: 
          $Is(M#2, Tclass._module.Stream(#$X))
               && $Is(N#2, Tclass._module.Stream(#$X))
               && $Is(P#2, Tclass._module.Stream(#$X))
               && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.append(#$X, $LS($LZ), M#2, _module.__default.append(#$X, $LS($LZ), N#2, P#2)), 
              _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#2, N#2), P#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(156,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Theorem4__Alt(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0), 
    P#0: DatatypeType
       where $Is(P#0, Tclass._module.Stream(#$X))
         && $IsAlloc(P#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(P#0));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem4__Alt(M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(#$X))
         && $IsAlloc(M#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#0), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.Stream(#$X))
         && $IsAlloc(N#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#0), 
    P#0: DatatypeType
       where $Is(P#0, Tclass._module.Stream(#$X))
         && $IsAlloc(P#0, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(P#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.append(#$X, $LS($LZ), M#0, _module.__default.append(#$X, $LS($LZ), N#0, P#0)))
     && $IsA#_module.Stream(_module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#0, N#0), P#0))
     && 
    _module.__default.append#canCall(#$X, N#0, P#0)
     && _module.__default.append#canCall(#$X, M#0, _module.__default.append(#$X, $LS($LZ), N#0, P#0))
     && 
    _module.__default.append#canCall(#$X, M#0, N#0)
     && _module.__default.append#canCall(#$X, _module.__default.append(#$X, $LS($LZ), M#0, N#0), P#0);
  ensures $Eq#_module.Stream(#$X, 
    #$X, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LS($LZ)), M#0, _module.__default.append(#$X, $LS($LS($LZ)), N#0, P#0)), 
    _module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#0, N#0), P#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1, N#1, P#1} CoCall$$_module.__default.Theorem4__Alt_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1), 
    N#1: DatatypeType
       where $Is(N#1, Tclass._module.Stream(#$X))
         && $IsAlloc(N#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#1), 
    P#1: DatatypeType
       where $Is(P#1, Tclass._module.Stream(#$X))
         && $IsAlloc(P#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(P#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, N#1, P#1)
     && _module.__default.append#canCall(#$X, M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1))
     && 
    _module.__default.append#canCall(#$X, M#1, N#1)
     && _module.__default.append#canCall(#$X, _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1);
  free ensures $PrefixEq#_module.Stream(#$X, 
    #$X, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
    _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1, N#1, P#1} Impl$$_module.__default.Theorem4__Alt_h(_k#0: Box, 
    M#1: DatatypeType
       where $Is(M#1, Tclass._module.Stream(#$X))
         && $IsAlloc(M#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(M#1), 
    N#1: DatatypeType
       where $Is(N#1, Tclass._module.Stream(#$X))
         && $IsAlloc(N#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(N#1), 
    P#1: DatatypeType
       where $Is(P#1, Tclass._module.Stream(#$X))
         && $IsAlloc(P#1, Tclass._module.Stream(#$X), $Heap)
         && $IsA#_module.Stream(P#1))
   returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.append#canCall(#$X, N#1, P#1)
     && _module.__default.append#canCall(#$X, M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1))
     && 
    _module.__default.append#canCall(#$X, M#1, N#1)
     && _module.__default.append#canCall(#$X, _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1);
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
      _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
       ==> _module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1)));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
      _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
       ==> _module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))
         && 
        _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
           == _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))
         && $PrefixEq#_module.Stream(#$X, 
          #$X, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1))), 
          _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))));
  ensures $PrefixEq#_module.Stream(#$X, 
      #$X, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
      _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
           ==> _module.Stream.Nil_q(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1)))
         && (_module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
           ==> _module.Stream.Cons_q(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))
             && 
            _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1)))
               == _module.Stream.head(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1))
             && $PrefixEq#_module.Stream(#$X, 
              #$X, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), M#1, _module.__default.append(#$X, $LS($LS($LZ)), N#1, P#1))), 
              _module.Stream.tail(_module.__default.append(#$X, $LS($LS($LZ)), _module.__default.append(#$X, $LS($LS($LZ)), M#1, N#1), P#1)))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(#$X, 
        #$X, 
        $LS($LS($LZ)), 
        _module.__default.append(#$X, $LS($LZ), M#1, _module.__default.append(#$X, $LS($LZ), N#1, P#1)), 
        _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#1, N#1), P#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1, N#1, P#1} Impl$$_module.__default.Theorem4__Alt_h(_k#0: Box, M#1: DatatypeType, N#1: DatatypeType, P#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: Box;
  var M##0: DatatypeType;
  var N##0: DatatypeType;
  var P##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Theorem4_Alt#, Impl$$_module.__default.Theorem4__Alt_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(165,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    assume $IsA#_module.Stream(N#1);
    assume $IsA#_module.Stream(P#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#M0#0: DatatypeType, 
        $ih#N0#0: DatatypeType, 
        $ih#P0#0: DatatypeType :: 
      $Is($ih#M0#0, Tclass._module.Stream(#$X))
           && $Is($ih#N0#0, Tclass._module.Stream(#$X))
           && $Is($ih#P0#0, Tclass._module.Stream(#$X))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(#$X, 
          #$X, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            $ih#M0#0, 
            _module.__default.append(#$X, $LS($LZ), $ih#N0#0, $ih#P0#0)), 
          _module.__default.append(#$X, 
            $LS($LZ), 
            _module.__default.append(#$X, $LS($LZ), $ih#M0#0, $ih#N0#0), 
            $ih#P0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(167,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(168,3)
        assume true;
        if (_module.Stream.Cons_q(M#1))
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(169,17)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assert _module.Stream.Cons_q(M#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := _module.Stream.tail(M#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            N##0 := N#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            P##0 := P#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Theorem4__Alt_h(_k##0, M##0, N##0, P##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(169,30)"} true;
        }
        else
        {
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(165,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, M#2: DatatypeType, N#2: DatatypeType, P#2: DatatypeType :: 
          $Is(M#2, Tclass._module.Stream(#$X))
               && $Is(N#2, Tclass._module.Stream(#$X))
               && $Is(P#2, Tclass._module.Stream(#$X))
               && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(#$X, 
              #$X, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.append(#$X, $LS($LZ), M#2, _module.__default.append(#$X, $LS($LZ), N#2, P#2)), 
              _module.__default.append(#$X, $LS($LZ), _module.__default.append(#$X, $LS($LZ), M#2, N#2), P#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(165,15)"} true;
    }
}



// function declaration for _module._default.FlattenStartMarker
function _module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T: Ty, M#0: DatatypeType, startMarker#0: Box)
   : DatatypeType;

function _module.__default.FlattenStartMarker#canCall(_module._default.FlattenStartMarker$T: Ty, M#0: DatatypeType, startMarker#0: Box)
   : bool;

// consequence axiom for _module.__default.FlattenStartMarker
axiom 44 <= $FunctionContextHeight
   ==> (forall _module._default.FlattenStartMarker$T: Ty, M#0: DatatypeType, startMarker#0: Box :: 
    { _module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, M#0, startMarker#0) } 
    _module.__default.FlattenStartMarker#canCall(_module._default.FlattenStartMarker$T, M#0, startMarker#0)
         || (44 != $FunctionContextHeight
           && 
          $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenStartMarker$T)))
           && $IsBox(startMarker#0, _module._default.FlattenStartMarker$T))
       ==> $Is(_module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, M#0, startMarker#0), 
        Tclass._module.Stream(_module._default.FlattenStartMarker$T)));

function _module.__default.FlattenStartMarker#requires(Ty, DatatypeType, Box) : bool;

// #requires axiom for _module.__default.FlattenStartMarker
axiom (forall _module._default.FlattenStartMarker$T: Ty, M#0: DatatypeType, startMarker#0: Box :: 
  { _module.__default.FlattenStartMarker#requires(_module._default.FlattenStartMarker$T, M#0, startMarker#0) } 
  $Is(M#0, 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenStartMarker$T)))
       && $IsBox(startMarker#0, _module._default.FlattenStartMarker$T)
     ==> _module.__default.FlattenStartMarker#requires(_module._default.FlattenStartMarker$T, M#0, startMarker#0)
       == true);

// definition axiom for _module.__default.FlattenStartMarker (revealed)
axiom 44 <= $FunctionContextHeight
   ==> (forall _module._default.FlattenStartMarker$T: Ty, M#0: DatatypeType, startMarker#0: Box :: 
    { _module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, M#0, startMarker#0) } 
    _module.__default.FlattenStartMarker#canCall(_module._default.FlattenStartMarker$T, M#0, startMarker#0)
         || (44 != $FunctionContextHeight
           && 
          $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenStartMarker$T)))
           && $IsBox(startMarker#0, _module._default.FlattenStartMarker$T))
       ==> _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.FlattenStartMarker$T, 
          Lit(#_module.Stream.Nil()), 
          M#0, 
          startMarker#0)
         && _module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, M#0, startMarker#0)
           == _module.__default.PrependThenFlattenStartMarker(_module._default.FlattenStartMarker$T, 
            $LS($LZ), 
            Lit(#_module.Stream.Nil()), 
            M#0, 
            startMarker#0));

// definition axiom for _module.__default.FlattenStartMarker for all literals (revealed)
axiom 44 <= $FunctionContextHeight
   ==> (forall _module._default.FlattenStartMarker$T: Ty, M#0: DatatypeType, startMarker#0: Box :: 
    {:weight 3} { _module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, Lit(M#0), Lit(startMarker#0)) } 
    _module.__default.FlattenStartMarker#canCall(_module._default.FlattenStartMarker$T, Lit(M#0), Lit(startMarker#0))
         || (44 != $FunctionContextHeight
           && 
          $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenStartMarker$T)))
           && $IsBox(startMarker#0, _module._default.FlattenStartMarker$T))
       ==> _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.FlattenStartMarker$T, 
          Lit(#_module.Stream.Nil()), 
          Lit(M#0), 
          Lit(startMarker#0))
         && _module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, Lit(M#0), Lit(startMarker#0))
           == Lit(_module.__default.PrependThenFlattenStartMarker(_module._default.FlattenStartMarker$T, 
              $LS($LZ), 
              Lit(#_module.Stream.Nil()), 
              Lit(M#0), 
              Lit(startMarker#0))));

procedure CheckWellformed$$_module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T: Ty, 
    M#0: DatatypeType
       where $Is(M#0, 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenStartMarker$T))), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.FlattenStartMarker$T));
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T: Ty, M#0: DatatypeType, startMarker#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##prefix#0: DatatypeType;
  var ##M#0: DatatypeType;
  var ##startMarker#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function FlattenStartMarker
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(193,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, M#0, startMarker#0), 
          Tclass._module.Stream(_module._default.FlattenStartMarker$T));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##prefix#0 := Lit(#_module.Stream.Nil());
        // assume allocatedness for argument to function
        assume $IsAlloc(##prefix#0, Tclass._module.Stream(_module._default.FlattenStartMarker$T), $Heap);
        ##M#0 := M#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenStartMarker$T)), 
          $Heap);
        ##startMarker#0 := startMarker#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##startMarker#0, _module._default.FlattenStartMarker$T, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.FlattenStartMarker$T, 
          Lit(#_module.Stream.Nil()), 
          M#0, 
          startMarker#0);
        assume _module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, M#0, startMarker#0)
           == _module.__default.PrependThenFlattenStartMarker(_module._default.FlattenStartMarker$T, 
            $LS($LZ), 
            Lit(#_module.Stream.Nil()), 
            M#0, 
            startMarker#0);
        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.FlattenStartMarker$T, 
          Lit(#_module.Stream.Nil()), 
          M#0, 
          startMarker#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.FlattenStartMarker(_module._default.FlattenStartMarker$T, M#0, startMarker#0), 
          Tclass._module.Stream(_module._default.FlattenStartMarker$T));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.PrependThenFlattenStartMarker
function _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T: Ty, 
    $ly: LayerType, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType, 
    startMarker#0: Box)
   : DatatypeType;

function _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T: Ty, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType, 
    startMarker#0: Box)
   : bool;

// layer synonym axiom
axiom (forall _module._default.PrependThenFlattenStartMarker$T: Ty, 
    $ly: LayerType, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType, 
    startMarker#0: Box :: 
  { _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
      $LS($ly), 
      prefix#0, 
      M#0, 
      startMarker#0) } 
  _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
      $LS($ly), 
      prefix#0, 
      M#0, 
      startMarker#0)
     == _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
      $ly, 
      prefix#0, 
      M#0, 
      startMarker#0));

// fuel synonym axiom
axiom (forall _module._default.PrependThenFlattenStartMarker$T: Ty, 
    $ly: LayerType, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType, 
    startMarker#0: Box :: 
  { _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
      AsFuelBottom($ly), 
      prefix#0, 
      M#0, 
      startMarker#0) } 
  _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
      $ly, 
      prefix#0, 
      M#0, 
      startMarker#0)
     == _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
      $LZ, 
      prefix#0, 
      M#0, 
      startMarker#0));

// consequence axiom for _module.__default.PrependThenFlattenStartMarker
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.PrependThenFlattenStartMarker$T: Ty, 
      $ly: LayerType, 
      prefix#0: DatatypeType, 
      M#0: DatatypeType, 
      startMarker#0: Box :: 
    { _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
        $ly, 
        prefix#0, 
        M#0, 
        startMarker#0) } 
    _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T, prefix#0, M#0, startMarker#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(prefix#0, 
            Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T))
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)))
           && $IsBox(startMarker#0, _module._default.PrependThenFlattenStartMarker$T))
       ==> $Is(_module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
          $ly, 
          prefix#0, 
          M#0, 
          startMarker#0), 
        Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)));

function _module.__default.PrependThenFlattenStartMarker#requires(Ty, LayerType, DatatypeType, DatatypeType, Box) : bool;

// #requires axiom for _module.__default.PrependThenFlattenStartMarker
axiom (forall _module._default.PrependThenFlattenStartMarker$T: Ty, 
    $ly: LayerType, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType, 
    startMarker#0: Box :: 
  { _module.__default.PrependThenFlattenStartMarker#requires(_module._default.PrependThenFlattenStartMarker$T, 
      $ly, 
      prefix#0, 
      M#0, 
      startMarker#0) } 
  $Is(prefix#0, 
        Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T))
       && $Is(M#0, 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)))
       && $IsBox(startMarker#0, _module._default.PrependThenFlattenStartMarker$T)
     ==> _module.__default.PrependThenFlattenStartMarker#requires(_module._default.PrependThenFlattenStartMarker$T, 
        $ly, 
        prefix#0, 
        M#0, 
        startMarker#0)
       == true);

// definition axiom for _module.__default.PrependThenFlattenStartMarker (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall _module._default.PrependThenFlattenStartMarker$T: Ty, 
      $ly: LayerType, 
      prefix#0: DatatypeType, 
      M#0: DatatypeType, 
      startMarker#0: Box :: 
    { _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
        $LS($ly), 
        prefix#0, 
        M#0, 
        startMarker#0) } 
    _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T, prefix#0, M#0, startMarker#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(prefix#0, 
            Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T))
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)))
           && $IsBox(startMarker#0, _module._default.PrependThenFlattenStartMarker$T))
       ==> (_module.Stream.Nil_q(prefix#0)
           ==> 
          !_module.Stream.Nil_q(M#0)
           ==> (var N#1 := _module.Stream.tail(M#0); 
            (var s#1 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
              _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T, s#1, N#1, startMarker#0))))
         && (!_module.Stream.Nil_q(prefix#0)
           ==> (var tl#1 := _module.Stream.tail(prefix#0); 
            _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T, tl#1, M#0, startMarker#0)))
         && _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
            $LS($ly), 
            prefix#0, 
            M#0, 
            startMarker#0)
           == (if _module.Stream.Nil_q(prefix#0)
             then (if _module.Stream.Nil_q(M#0)
               then #_module.Stream.Nil()
               else (var N#0 := _module.Stream.tail(M#0); 
                (var s#0 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                  #_module.Stream.Cons(startMarker#0, 
                    _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, $ly, s#0, N#0, startMarker#0)))))
             else (var tl#0 := _module.Stream.tail(prefix#0); 
              (var hd#0 := _module.Stream.head(prefix#0); 
                #_module.Stream.Cons(hd#0, 
                  _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, $ly, tl#0, M#0, startMarker#0))))));

procedure CheckWellformed$$_module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T: Ty, 
    prefix#0: DatatypeType
       where $Is(prefix#0, 
        Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)), 
    M#0: DatatypeType
       where $Is(M#0, 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T))), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.PrependThenFlattenStartMarker$T));
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T: Ty, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType, 
    startMarker#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tl#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var hd#Z#0: Box;
  var let#1#0#0: Box;
  var ##prefix#0: DatatypeType;
  var ##M#0: DatatypeType;
  var ##startMarker#0: Box;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var N#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var s#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var ##prefix#1: DatatypeType;
  var ##M#1: DatatypeType;
  var ##startMarker#1: Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function PrependThenFlattenStartMarker
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(198,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
            $LS($LZ), 
            prefix#0, 
            M#0, 
            startMarker#0), 
          Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (prefix#0 == #_module.Stream.Nil())
        {
            if (M#0 == #_module.Stream.Nil())
            {
                assume _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
                    $LS($LZ), 
                    prefix#0, 
                    M#0, 
                    startMarker#0)
                   == Lit(#_module.Stream.Nil());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
                    $LS($LZ), 
                    prefix#0, 
                    M#0, 
                    startMarker#0), 
                  Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
            }
            else if (M#0 == #_module.Stream.Cons($Box(_mcc#2#0), _mcc#3#0))
            {
                assume $Is(_mcc#2#0, 
                  Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
                assume $Is(_mcc#3#0, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)));
                havoc N#Z#0;
                assume $Is(N#Z#0, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)));
                assume let#2#0#0 == _mcc#3#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)));
                assume N#Z#0 == let#2#0#0;
                havoc s#Z#0;
                assume $Is(s#Z#0, Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
                assume let#3#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#3#0#0, 
                  Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
                assume s#Z#0 == let#3#0#0;
                ##prefix#1 := s#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##prefix#1, 
                  Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T), 
                  $Heap);
                ##M#1 := N#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##M#1, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)), 
                  $Heap);
                ##startMarker#1 := startMarker#0;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##startMarker#1, _module._default.PrependThenFlattenStartMarker$T, $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T, s#Z#0, N#Z#0, startMarker#0);
                assume _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
                    $LS($LZ), 
                    prefix#0, 
                    M#0, 
                    startMarker#0)
                   == #_module.Stream.Cons(startMarker#0, 
                    _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
                      $LS($LZ), 
                      s#Z#0, 
                      N#Z#0, 
                      startMarker#0));
                assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T, s#Z#0, N#Z#0, startMarker#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
                    $LS($LZ), 
                    prefix#0, 
                    M#0, 
                    startMarker#0), 
                  Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
            }
            else
            {
                assume false;
            }
        }
        else if (prefix#0 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.PrependThenFlattenStartMarker$T);
            assume $Is(_mcc#1#0, 
              Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
            havoc tl#Z#0;
            assume $Is(tl#Z#0, Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, 
              Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
            assume tl#Z#0 == let#0#0#0;
            havoc hd#Z#0;
            assume $IsBox(hd#Z#0, _module._default.PrependThenFlattenStartMarker$T);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, _module._default.PrependThenFlattenStartMarker$T);
            assume hd#Z#0 == let#1#0#0;
            ##prefix#0 := tl#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##prefix#0, 
              Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T), 
              $Heap);
            ##M#0 := M#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##M#0, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T)), 
              $Heap);
            ##startMarker#0 := startMarker#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##startMarker#0, _module._default.PrependThenFlattenStartMarker$T, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T, tl#Z#0, M#0, startMarker#0);
            assume _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
                $LS($LZ), 
                prefix#0, 
                M#0, 
                startMarker#0)
               == #_module.Stream.Cons(hd#Z#0, 
                _module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
                  $LS($LZ), 
                  tl#Z#0, 
                  M#0, 
                  startMarker#0));
            assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.PrependThenFlattenStartMarker$T, tl#Z#0, M#0, startMarker#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.PrependThenFlattenStartMarker(_module._default.PrependThenFlattenStartMarker$T, 
                $LS($LZ), 
                prefix#0, 
                M#0, 
                startMarker#0), 
              Tclass._module.Stream(_module._default.PrependThenFlattenStartMarker$T));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.StreamOfNonEmpties
function _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0: Ty, $ly: LayerType, M#0: DatatypeType)
   : bool;

function _module.__default.StreamOfNonEmpties#canCall(_module._default.StreamOfNonEmpties$_T0: Ty, M#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.StreamOfNonEmpties$_T0: Ty, $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($ly), M#0) } 
  _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($ly), M#0)
     == _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $ly, M#0));

// fuel synonym axiom
axiom (forall _module._default.StreamOfNonEmpties$_T0: Ty, $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, AsFuelBottom($ly), M#0) } 
  _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $ly, M#0)
     == _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LZ, M#0));

// consequence axiom for _module.__default.StreamOfNonEmpties
axiom 23 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties$_T0: Ty, $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $ly, M#0) } 
    _module.__default.StreamOfNonEmpties#canCall(_module._default.StreamOfNonEmpties$_T0, M#0)
         || (23 != $FunctionContextHeight
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0))))
       ==> true);

function _module.__default.StreamOfNonEmpties#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.StreamOfNonEmpties
axiom (forall _module._default.StreamOfNonEmpties$_T0: Ty, $ly: LayerType, M#0: DatatypeType :: 
  { _module.__default.StreamOfNonEmpties#requires(_module._default.StreamOfNonEmpties$_T0, $ly, M#0) } 
  $Is(M#0, 
      Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0)))
     ==> _module.__default.StreamOfNonEmpties#requires(_module._default.StreamOfNonEmpties$_T0, $ly, M#0)
       == true);

// definition axiom for _module.__default.StreamOfNonEmpties (revealed)
axiom 23 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties$_T0: Ty, $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($ly), M#0) } 
    _module.__default.StreamOfNonEmpties#canCall(_module._default.StreamOfNonEmpties$_T0, M#0)
         || (23 != $FunctionContextHeight
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0))))
       ==> (!_module.Stream.Nil_q(M#0)
           ==> (var N#1 := _module.Stream.tail(M#0); 
            (var s#1 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
              _module.Stream.Cons_q(s#1)
                 ==> _module.__default.StreamOfNonEmpties#canCall(_module._default.StreamOfNonEmpties$_T0, N#1))))
         && _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($ly), M#0)
           == (if _module.Stream.Nil_q(M#0)
             then true
             else (var N#0 := _module.Stream.tail(M#0); 
              (var s#0 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                _module.Stream.Cons_q(s#0)
                   && _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $ly, N#0)))));

// 1st prefix predicate axiom for _module.__default.StreamOfNonEmpties_h
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties#$_T0: Ty, $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), M#0) } 
    $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties#$_T0)))
         && _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), M#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k#0, M#0) } 
        _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k#0, M#0)));

// 2nd prefix predicate axiom
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties#$_T0: Ty, $ly: LayerType, M#0: DatatypeType :: 
    { _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), M#0) } 
    $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties#$_T0)))
         && (forall _k#0: Box :: 
          { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k#0, M#0) } 
          _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k#0, M#0))
       ==> _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), M#0));

// 3rd prefix predicate axiom
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties#$_T0: Ty, 
      $ly: LayerType, 
      M#0: DatatypeType, 
      _k#0: Box :: 
    { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $ly, _k#0, M#0) } 
    $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties#$_T0)))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $ly, _k#0, M#0));

procedure CheckWellformed$$_module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0: Ty, 
    M#0: DatatypeType
       where $Is(M#0, 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0))));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0: Ty, M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var N#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var s#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##M#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function StreamOfNonEmpties
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(211,19): initial state"} true;
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
        if (M#0 == #_module.Stream.Nil())
        {
            assume _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($LZ), M#0)
               == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($LZ), M#0), 
              TBool);
        }
        else if (M#0 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0));
            assume $Is(_mcc#1#0, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0)));
            havoc N#Z#0;
            assume $Is(N#Z#0, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0)));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0)));
            assume N#Z#0 == let#0#0#0;
            havoc s#Z#0;
            assume $Is(s#Z#0, Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0));
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0));
            assume s#Z#0 == let#1#0#0;
            if (_module.Stream.Cons_q(s#Z#0))
            {
                ##M#0 := N#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##M#0, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties$_T0)), 
                  $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.StreamOfNonEmpties#canCall(_module._default.StreamOfNonEmpties$_T0, N#Z#0);
            }

            assume _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($LZ), M#0)
               == (_module.Stream.Cons_q(s#Z#0)
                 && _module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($LZ), N#Z#0));
            assume _module.Stream.Cons_q(s#Z#0)
               ==> _module.__default.StreamOfNonEmpties#canCall(_module._default.StreamOfNonEmpties$_T0, N#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.StreamOfNonEmpties(_module._default.StreamOfNonEmpties$_T0, $LS($LZ), M#0), 
              TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.StreamOfNonEmpties#
function _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    M#0: DatatypeType)
   : bool;

function _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0: Ty, _k#0: Box, M#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.StreamOfNonEmpties#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    M#0: DatatypeType :: 
  { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k#0, M#0) } 
  _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k#0, M#0)
     == _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $ly, _k#0, M#0));

// fuel synonym axiom
axiom (forall _module._default.StreamOfNonEmpties#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    M#0: DatatypeType :: 
  { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, AsFuelBottom($ly), _k#0, M#0) } 
  _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $ly, _k#0, M#0)
     == _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LZ, _k#0, M#0));

// consequence axiom for _module.__default.StreamOfNonEmpties_h
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      M#0: DatatypeType :: 
    { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $ly, _k#0, M#0) } 
    _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, _k#0, M#0)
         || (24 != $FunctionContextHeight
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties#$_T0))))
       ==> true);

function _module.__default.StreamOfNonEmpties_h#requires(Ty, LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.StreamOfNonEmpties_h
axiom (forall _module._default.StreamOfNonEmpties#$_T0: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    M#0: DatatypeType :: 
  { _module.__default.StreamOfNonEmpties_h#requires(_module._default.StreamOfNonEmpties#$_T0, $ly, _k#0, M#0) } 
  $Is(M#0, 
      Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties#$_T0)))
     ==> _module.__default.StreamOfNonEmpties_h#requires(_module._default.StreamOfNonEmpties#$_T0, $ly, _k#0, M#0)
       == true);

// definition axiom for _module.__default.StreamOfNonEmpties_h (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      M#0: DatatypeType :: 
    { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k#0, M#0) } 
    _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, _k#0, M#0)
         || (24 != $FunctionContextHeight
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties#$_T0))))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(M#0)
           ==> (var N#3 := _module.Stream.tail(M#0); 
            (var s#3 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
              _module.Stream.Cons_q(s#3)
                 ==> _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, ORD#Minus(_k#0, ORD#FromNat(1)), N#3))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(M#0)
             then true
             else (var N#4 := _module.Stream.tail(M#0); 
              (var s#4 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                _module.Stream.Cons_q(s#4)
                   && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, 
                    $ly, 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    N#4)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $ly, _k'#0, M#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, _k'#0, M#0)))
         && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k#0, M#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(M#0)
                 then true
                 else (var N#2 := _module.Stream.tail(M#0); 
                  (var s#2 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                    _module.Stream.Cons_q(s#2)
                       && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, 
                        $ly, 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        N#2)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $ly, _k'#0, M#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $ly, _k'#0, M#0)))));

// definition axiom for _module.__default.StreamOfNonEmpties_h for decreasing-related literals (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      M#0: DatatypeType :: 
    {:weight 3} { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), Lit(_k#0), M#0) } 
    _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, Lit(_k#0), M#0)
         || (24 != $FunctionContextHeight
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties#$_T0))))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(M#0)
           ==> (var N#6 := _module.Stream.tail(M#0); 
            (var s#6 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
              _module.Stream.Cons_q(s#6)
                 ==> _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, ORD#Minus(_k#0, ORD#FromNat(1)), N#6))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(M#0)
             then true
             else (var N#7 := _module.Stream.tail(M#0); 
              (var s#7 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                _module.Stream.Cons_q(s#7)
                   && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, 
                    $LS($ly), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    N#7)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k'#1, M#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, _k'#1, M#0)))
         && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), Lit(_k#0), M#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(M#0)
                 then true
                 else (var N#5 := _module.Stream.tail(M#0); 
                  (var s#5 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                    _module.Stream.Cons_q(s#5)
                       && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, 
                        $LS($ly), 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        N#5)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k'#1, M#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k'#1, M#0)))));

// definition axiom for _module.__default.StreamOfNonEmpties_h for all literals (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.StreamOfNonEmpties#$_T0: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      M#0: DatatypeType :: 
    {:weight 3} { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), Lit(_k#0), Lit(M#0)) } 
    _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, Lit(_k#0), Lit(M#0))
         || (24 != $FunctionContextHeight
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.StreamOfNonEmpties#$_T0))))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(M#0)
           ==> (var N#9 := _module.Stream.tail(M#0); 
            (var s#9 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
              _module.Stream.Cons_q(s#9)
                 ==> _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, ORD#Minus(_k#0, ORD#FromNat(1)), N#9))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(M#0)
             then true
             else (var N#10 := _module.Stream.tail(M#0); 
              (var s#10 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                _module.Stream.Cons_q(s#10)
                   && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, 
                    $LS($ly), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    N#10)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k'#2, M#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.StreamOfNonEmpties_h#canCall(_module._default.StreamOfNonEmpties#$_T0, _k'#2, M#0)))
         && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), Lit(_k#0), Lit(M#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(M#0)
                 then true
                 else (var N#8 := _module.Stream.tail(M#0); 
                  (var s#8 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                    _module.Stream.Cons_q(s#8)
                       && _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, 
                        $LS($ly), 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        N#8)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k'#2, M#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.StreamOfNonEmpties_h(_module._default.StreamOfNonEmpties#$_T0, $LS($ly), _k'#2, M#0)))));

// function declaration for _module._default.FlattenNonEmpties
function _module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0: Ty, M#0: DatatypeType) : DatatypeType;

function _module.__default.FlattenNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0: Ty, M#0: DatatypeType) : bool;

// consequence axiom for _module.__default.FlattenNonEmpties
axiom 45 <= $FunctionContextHeight
   ==> (forall _module._default.FlattenNonEmpties$_T0: Ty, M#0: DatatypeType :: 
    { _module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, M#0) } 
    _module.__default.FlattenNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0, M#0)
         || (45 != $FunctionContextHeight
           && 
          $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0)))
           && _module.__default.StreamOfNonEmpties(_module._default.FlattenNonEmpties$_T0, $LS($LZ), M#0))
       ==> $Is(_module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, M#0), 
        Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0)));

function _module.__default.FlattenNonEmpties#requires(Ty, DatatypeType) : bool;

// #requires axiom for _module.__default.FlattenNonEmpties
axiom (forall _module._default.FlattenNonEmpties$_T0: Ty, M#0: DatatypeType :: 
  { _module.__default.FlattenNonEmpties#requires(_module._default.FlattenNonEmpties$_T0, M#0) } 
  $Is(M#0, 
      Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0)))
     ==> _module.__default.FlattenNonEmpties#requires(_module._default.FlattenNonEmpties$_T0, M#0)
       == _module.__default.StreamOfNonEmpties(_module._default.FlattenNonEmpties$_T0, $LS($LZ), M#0));

// definition axiom for _module.__default.FlattenNonEmpties (revealed)
axiom 45 <= $FunctionContextHeight
   ==> (forall _module._default.FlattenNonEmpties$_T0: Ty, M#0: DatatypeType :: 
    { _module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, M#0) } 
    _module.__default.FlattenNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0, M#0)
         || (45 != $FunctionContextHeight
           && 
          $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0)))
           && _module.__default.StreamOfNonEmpties(_module._default.FlattenNonEmpties$_T0, $LS($LZ), M#0))
       ==> _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0, Lit(#_module.Stream.Nil()), M#0)
         && _module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, M#0)
           == _module.__default.PrependThenFlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, 
            $LS($LZ), 
            Lit(#_module.Stream.Nil()), 
            M#0));

// definition axiom for _module.__default.FlattenNonEmpties for all literals (revealed)
axiom 45 <= $FunctionContextHeight
   ==> (forall _module._default.FlattenNonEmpties$_T0: Ty, M#0: DatatypeType :: 
    {:weight 3} { _module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, Lit(M#0)) } 
    _module.__default.FlattenNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0, Lit(M#0))
         || (45 != $FunctionContextHeight
           && 
          $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0)))
           && Lit(_module.__default.StreamOfNonEmpties(_module._default.FlattenNonEmpties$_T0, $LS($LZ), Lit(M#0))))
       ==> _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0, Lit(#_module.Stream.Nil()), Lit(M#0))
         && _module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, Lit(M#0))
           == Lit(_module.__default.PrependThenFlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, 
              $LS($LZ), 
              Lit(#_module.Stream.Nil()), 
              Lit(M#0))));

procedure CheckWellformed$$_module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0: Ty, 
    M#0: DatatypeType
       where $Is(M#0, 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0))));
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0: Ty, M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##M#0: DatatypeType;
  var b$reqreads#0: bool;
  var ##prefix#0: DatatypeType;
  var ##M#1: DatatypeType;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function FlattenNonEmpties
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(218,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##M#0 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#0, 
      Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0)), 
      $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.StreamOfNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0, M#0);
    assume _module.__default.StreamOfNonEmpties(_module._default.FlattenNonEmpties$_T0, $LS($LZ), M#0);
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, M#0), 
          Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##prefix#0 := Lit(#_module.Stream.Nil());
        // assume allocatedness for argument to function
        assume $IsAlloc(##prefix#0, Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0), $Heap);
        ##M#1 := M#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0)), 
          $Heap);
        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.FlattenNonEmpties$_T0, $LS($LS($LZ)), ##M#1);
        assume _module.__default.StreamOfNonEmpties(_module._default.FlattenNonEmpties$_T0, $LS($LZ), ##M#1);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0, Lit(#_module.Stream.Nil()), M#0);
        assume _module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, M#0)
           == _module.__default.PrependThenFlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, 
            $LS($LZ), 
            Lit(#_module.Stream.Nil()), 
            M#0);
        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.FlattenNonEmpties$_T0, Lit(#_module.Stream.Nil()), M#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.FlattenNonEmpties(_module._default.FlattenNonEmpties$_T0, M#0), 
          Tclass._module.Stream(_module._default.FlattenNonEmpties$_T0));
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.PrependThenFlattenNonEmpties
function _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
    $ly: LayerType, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType)
   : DatatypeType;

function _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
    $ly: LayerType, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType :: 
  { _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($ly), prefix#0, M#0) } 
  _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($ly), prefix#0, M#0)
     == _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $ly, prefix#0, M#0));

// fuel synonym axiom
axiom (forall _module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
    $ly: LayerType, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType :: 
  { _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, 
      AsFuelBottom($ly), 
      prefix#0, 
      M#0) } 
  _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $ly, prefix#0, M#0)
     == _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LZ, prefix#0, M#0));

// consequence axiom for _module.__default.PrependThenFlattenNonEmpties
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
      $ly: LayerType, 
      prefix#0: DatatypeType, 
      M#0: DatatypeType :: 
    { _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $ly, prefix#0, M#0) } 
    _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, prefix#0, M#0)
         || (29 != $FunctionContextHeight
           && 
          $Is(prefix#0, 
            Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0))
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)))
           && _module.__default.StreamOfNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), M#0))
       ==> $Is(_module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $ly, prefix#0, M#0), 
        Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)));

function _module.__default.PrependThenFlattenNonEmpties#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.PrependThenFlattenNonEmpties
axiom (forall _module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
    $ly: LayerType, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType :: 
  { _module.__default.PrependThenFlattenNonEmpties#requires(_module._default.PrependThenFlattenNonEmpties$_T0, $ly, prefix#0, M#0) } 
  $Is(prefix#0, 
        Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0))
       && $Is(M#0, 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)))
     ==> _module.__default.PrependThenFlattenNonEmpties#requires(_module._default.PrependThenFlattenNonEmpties$_T0, $ly, prefix#0, M#0)
       == _module.__default.StreamOfNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), M#0));

// definition axiom for _module.__default.PrependThenFlattenNonEmpties (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
      $ly: LayerType, 
      prefix#0: DatatypeType, 
      M#0: DatatypeType :: 
    { _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($ly), prefix#0, M#0) } 
    _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, prefix#0, M#0)
         || (29 != $FunctionContextHeight
           && 
          $Is(prefix#0, 
            Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0))
           && $Is(M#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)))
           && _module.__default.StreamOfNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), M#0))
       ==> (_module.Stream.Nil_q(prefix#0)
           ==> 
          !_module.Stream.Nil_q(M#0)
           ==> (var N#1 := _module.Stream.tail(M#0); 
            (var s#1 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
              _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, _module.Stream.tail(s#1), N#1))))
         && (!_module.Stream.Nil_q(prefix#0)
           ==> (var tl#1 := _module.Stream.tail(prefix#0); 
            _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, tl#1, M#0)))
         && _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($ly), prefix#0, M#0)
           == (if _module.Stream.Nil_q(prefix#0)
             then (if _module.Stream.Nil_q(M#0)
               then #_module.Stream.Nil()
               else (var N#0 := _module.Stream.tail(M#0); 
                (var s#0 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                  #_module.Stream.Cons(_module.Stream.head(s#0), 
                    _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, 
                      $ly, 
                      _module.Stream.tail(s#0), 
                      N#0)))))
             else (var tl#0 := _module.Stream.tail(prefix#0); 
              (var hd#0 := _module.Stream.head(prefix#0); 
                #_module.Stream.Cons(hd#0, 
                  _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $ly, tl#0, M#0))))));

procedure CheckWellformed$$_module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
    prefix#0: DatatypeType
       where $Is(prefix#0, 
        Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)), 
    M#0: DatatypeType
       where $Is(M#0, 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0))));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0: Ty, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##M#0: DatatypeType;
  var b$reqreads#0: bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tl#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var hd#Z#0: Box;
  var let#1#0#0: Box;
  var ##prefix#0: DatatypeType;
  var ##M#1: DatatypeType;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var N#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var s#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var ##prefix#1: DatatypeType;
  var ##M#2: DatatypeType;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function PrependThenFlattenNonEmpties
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(224,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##M#0 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#0, 
      Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)), 
      $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.StreamOfNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, M#0);
    assume _module.__default.StreamOfNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), M#0);
    assert b$reqreads#0;
    if (*)
    {
        assume $Is(_module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), prefix#0, M#0), 
          Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (prefix#0 == #_module.Stream.Nil())
        {
            if (M#0 == #_module.Stream.Nil())
            {
                assume _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), prefix#0, M#0)
                   == Lit(#_module.Stream.Nil());
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), prefix#0, M#0), 
                  Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
            }
            else if (M#0 == #_module.Stream.Cons($Box(_mcc#2#0), _mcc#3#0))
            {
                assume $Is(_mcc#2#0, 
                  Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
                assume $Is(_mcc#3#0, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)));
                havoc N#Z#0;
                assume $Is(N#Z#0, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)));
                assume let#2#0#0 == _mcc#3#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)));
                assume N#Z#0 == let#2#0#0;
                havoc s#Z#0;
                assume $Is(s#Z#0, Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
                assume let#3#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#3#0#0, 
                  Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
                assume s#Z#0 == let#3#0#0;
                assert _module.Stream.Cons_q(s#Z#0);
                assert _module.Stream.Cons_q(s#Z#0);
                ##prefix#1 := _module.Stream.tail(s#Z#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##prefix#1, 
                  Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0), 
                  $Heap);
                ##M#2 := N#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##M#2, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)), 
                  $Heap);
                assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LS($LZ)), ##M#2);
                assume _module.__default.StreamOfNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), ##M#2);
                b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, 
                  _module.Stream.tail(s#Z#0), 
                  N#Z#0);
                assume _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), prefix#0, M#0)
                   == #_module.Stream.Cons(_module.Stream.head(s#Z#0), 
                    _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, 
                      $LS($LZ), 
                      _module.Stream.tail(s#Z#0), 
                      N#Z#0));
                assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, 
                  _module.Stream.tail(s#Z#0), 
                  N#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), prefix#0, M#0), 
                  Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
            }
            else
            {
                assume false;
            }
        }
        else if (prefix#0 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.PrependThenFlattenNonEmpties$_T0);
            assume $Is(_mcc#1#0, 
              Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
            havoc tl#Z#0;
            assume $Is(tl#Z#0, Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, 
              Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
            assume tl#Z#0 == let#0#0#0;
            havoc hd#Z#0;
            assume $IsBox(hd#Z#0, _module._default.PrependThenFlattenNonEmpties$_T0);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, _module._default.PrependThenFlattenNonEmpties$_T0);
            assume hd#Z#0 == let#1#0#0;
            ##prefix#0 := tl#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##prefix#0, 
              Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0), 
              $Heap);
            ##M#1 := M#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##M#1, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0)), 
              $Heap);
            assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LS($LZ)), ##M#1);
            assume _module.__default.StreamOfNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), ##M#1);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, tl#Z#0, M#0);
            assume _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), prefix#0, M#0)
               == #_module.Stream.Cons(hd#Z#0, 
                _module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), tl#Z#0, M#0));
            assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.PrependThenFlattenNonEmpties$_T0, tl#Z#0, M#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.PrependThenFlattenNonEmpties(_module._default.PrependThenFlattenNonEmpties$_T0, $LS($LZ), prefix#0, M#0), 
              Tclass._module.Stream(_module._default.PrependThenFlattenNonEmpties$_T0));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.Prepend
function _module.__default.Prepend(_module._default.Prepend$T: Ty, $ly: LayerType, x#0: Box, M#0: DatatypeType)
   : DatatypeType;

function _module.__default.Prepend#canCall(_module._default.Prepend$T: Ty, x#0: Box, M#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.Prepend$T: Ty, $ly: LayerType, x#0: Box, M#0: DatatypeType :: 
  { _module.__default.Prepend(_module._default.Prepend$T, $LS($ly), x#0, M#0) } 
  _module.__default.Prepend(_module._default.Prepend$T, $LS($ly), x#0, M#0)
     == _module.__default.Prepend(_module._default.Prepend$T, $ly, x#0, M#0));

// fuel synonym axiom
axiom (forall _module._default.Prepend$T: Ty, $ly: LayerType, x#0: Box, M#0: DatatypeType :: 
  { _module.__default.Prepend(_module._default.Prepend$T, AsFuelBottom($ly), x#0, M#0) } 
  _module.__default.Prepend(_module._default.Prepend$T, $ly, x#0, M#0)
     == _module.__default.Prepend(_module._default.Prepend$T, $LZ, x#0, M#0));

// consequence axiom for _module.__default.Prepend
axiom 25 <= $FunctionContextHeight
   ==> (forall _module._default.Prepend$T: Ty, $ly: LayerType, x#0: Box, M#0: DatatypeType :: 
    { _module.__default.Prepend(_module._default.Prepend$T, $ly, x#0, M#0) } 
    _module.__default.Prepend#canCall(_module._default.Prepend$T, x#0, M#0)
         || (25 != $FunctionContextHeight
           && 
          $IsBox(x#0, _module._default.Prepend$T)
           && $Is(M#0, Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T))))
       ==> $Is(_module.__default.Prepend(_module._default.Prepend$T, $ly, x#0, M#0), 
        Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T))));

function _module.__default.Prepend#requires(Ty, LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.Prepend
axiom (forall _module._default.Prepend$T: Ty, $ly: LayerType, x#0: Box, M#0: DatatypeType :: 
  { _module.__default.Prepend#requires(_module._default.Prepend$T, $ly, x#0, M#0) } 
  $IsBox(x#0, _module._default.Prepend$T)
       && $Is(M#0, Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T)))
     ==> _module.__default.Prepend#requires(_module._default.Prepend$T, $ly, x#0, M#0)
       == true);

// definition axiom for _module.__default.Prepend (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall _module._default.Prepend$T: Ty, $ly: LayerType, x#0: Box, M#0: DatatypeType :: 
    { _module.__default.Prepend(_module._default.Prepend$T, $LS($ly), x#0, M#0) } 
    _module.__default.Prepend#canCall(_module._default.Prepend$T, x#0, M#0)
         || (25 != $FunctionContextHeight
           && 
          $IsBox(x#0, _module._default.Prepend$T)
           && $Is(M#0, Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T))))
       ==> (!_module.Stream.Nil_q(M#0)
           ==> (var N#1 := _module.Stream.tail(M#0); 
            _module.__default.Prepend#canCall(_module._default.Prepend$T, x#0, N#1)))
         && _module.__default.Prepend(_module._default.Prepend$T, $LS($ly), x#0, M#0)
           == (if _module.Stream.Nil_q(M#0)
             then #_module.Stream.Nil()
             else (var N#0 := _module.Stream.tail(M#0); 
              (var s#0 := $Unbox(_module.Stream.head(M#0)): DatatypeType; 
                #_module.Stream.Cons($Box(#_module.Stream.Cons(x#0, s#0)), 
                  _module.__default.Prepend(_module._default.Prepend$T, $ly, x#0, N#0))))));

procedure CheckWellformed$$_module.__default.Prepend(_module._default.Prepend$T: Ty, 
    x#0: Box where $IsBox(x#0, _module._default.Prepend$T), 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T))));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Prepend(_module._default.Prepend$T: Ty, x#0: Box, M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var N#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var s#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##x#0: Box;
  var ##M#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Prepend
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(240,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Prepend(_module._default.Prepend$T, $LS($LZ), x#0, M#0), 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T)));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (M#0 == #_module.Stream.Nil())
        {
            assume _module.__default.Prepend(_module._default.Prepend$T, $LS($LZ), x#0, M#0)
               == Lit(#_module.Stream.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Prepend(_module._default.Prepend$T, $LS($LZ), x#0, M#0), 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T)));
        }
        else if (M#0 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Stream(_module._default.Prepend$T));
            assume $Is(_mcc#1#0, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T)));
            havoc N#Z#0;
            assume $Is(N#Z#0, Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T)));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T)));
            assume N#Z#0 == let#0#0#0;
            havoc s#Z#0;
            assume $Is(s#Z#0, Tclass._module.Stream(_module._default.Prepend$T));
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Stream(_module._default.Prepend$T));
            assume s#Z#0 == let#1#0#0;
            ##x#0 := x#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#0, _module._default.Prepend$T, $Heap);
            ##M#0 := N#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##M#0, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T)), 
              $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Prepend#canCall(_module._default.Prepend$T, x#0, N#Z#0);
            assume _module.__default.Prepend(_module._default.Prepend$T, $LS($LZ), x#0, M#0)
               == #_module.Stream.Cons($Box(#_module.Stream.Cons(x#0, s#Z#0)), 
                _module.__default.Prepend(_module._default.Prepend$T, $LS($LZ), x#0, N#Z#0));
            assume _module.__default.Prepend#canCall(_module._default.Prepend$T, x#0, N#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Prepend(_module._default.Prepend$T, $LS($LZ), x#0, M#0), 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend$T)));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.Prepend__Lemma(_module._default.Prepend_Lemma$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Prepend_Lemma$T)
         && $IsAllocBox(x#0, _module._default.Prepend_Lemma$T, $Heap), 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Prepend__Lemma(_module._default.Prepend_Lemma$T: Ty, 
    x#0: Box
       where $IsBox(x#0, _module._default.Prepend_Lemma$T)
         && $IsAllocBox(x#0, _module._default.Prepend_Lemma$T, $Heap), 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Prepend#canCall(_module._default.Prepend_Lemma$T, x#0, M#0)
     && _module.__default.StreamOfNonEmpties#canCall(_module._default.Prepend_Lemma$T, 
      _module.__default.Prepend(_module._default.Prepend_Lemma$T, $LS($LZ), x#0, M#0));
  ensures _module.__default.StreamOfNonEmpties(_module._default.Prepend_Lemma$T, 
    $LS($LS($LZ)), 
    _module.__default.Prepend(_module._default.Prepend_Lemma$T, $LS($LS($LZ)), x#0, M#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} CoCall$$_module.__default.Prepend__Lemma_h(_module._default.Prepend_Lemma#$T: Ty, 
    _k#0: Box, 
    x#1: Box
       where $IsBox(x#1, _module._default.Prepend_Lemma#$T)
         && $IsAllocBox(x#1, _module._default.Prepend_Lemma#$T, $Heap), 
    M#1: DatatypeType
       where $Is(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)))
         && $IsAlloc(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)), 
          $Heap)
         && $IsA#_module.Stream(M#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Prepend#canCall(_module._default.Prepend_Lemma#$T, x#1, M#1)
     && _module.__default.StreamOfNonEmpties_h#canCall(_module._default.Prepend_Lemma#$T, 
      _k#0, 
      _module.__default.Prepend(_module._default.Prepend_Lemma#$T, $LS($LZ), x#1, M#1));
  ensures _module.__default.StreamOfNonEmpties_h(_module._default.Prepend_Lemma#$T, 
    $LS($LS($LZ)), 
    _k#0, 
    _module.__default.Prepend(_module._default.Prepend_Lemma#$T, $LS($LS($LZ)), x#1, M#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, M#1} Impl$$_module.__default.Prepend__Lemma_h(_module._default.Prepend_Lemma#$T: Ty, 
    _k#0: Box, 
    x#1: Box
       where $IsBox(x#1, _module._default.Prepend_Lemma#$T)
         && $IsAllocBox(x#1, _module._default.Prepend_Lemma#$T, $Heap), 
    M#1: DatatypeType
       where $Is(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)))
         && $IsAlloc(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)), 
          $Heap)
         && $IsA#_module.Stream(M#1))
   returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Prepend#canCall(_module._default.Prepend_Lemma#$T, x#1, M#1)
     && _module.__default.StreamOfNonEmpties_h#canCall(_module._default.Prepend_Lemma#$T, 
      _k#0, 
      _module.__default.Prepend(_module._default.Prepend_Lemma#$T, $LS($LZ), x#1, M#1));
  ensures _module.__default.StreamOfNonEmpties_h(_module._default.Prepend_Lemma#$T, 
    $LS($LS($LZ)), 
    _k#0, 
    _module.__default.Prepend(_module._default.Prepend_Lemma#$T, $LS($LS($LZ)), x#1, M#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, M#1} Impl$$_module.__default.Prepend__Lemma_h(_module._default.Prepend_Lemma#$T: Ty, _k#0: Box, x#1: Box, M#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var N#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var s#0: DatatypeType;
  var let#0_0_1#0#0: DatatypeType;
  var _k##0: Box;
  var x##0: Box;
  var M##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Prepend_Lemma#, Impl$$_module.__default.Prepend__Lemma_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(247,15): initial state"} true;
    assume $IsA#_module.Stream(M#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#M0#0: DatatypeType :: 
      $Is($ih#M0#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.StreamOfNonEmpties_h(_module._default.Prepend_Lemma#$T, 
          $LS($LZ), 
          $ih#_k0#0, 
          _module.__default.Prepend(_module._default.Prepend_Lemma#$T, $LS($LZ), x#1, $ih#M0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(249,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (M#1 == #_module.Stream.Nil())
        {
        }
        else if (M#1 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Stream(_module._default.Prepend_Lemma#$T))
               && $IsAlloc(_mcc#0#0, Tclass._module.Stream(_module._default.Prepend_Lemma#$T), $Heap);
            assume $Is(_mcc#1#0, 
                Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)))
               && $IsAlloc(_mcc#1#0, 
                Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)), 
                $Heap);
            havoc N#0;
            assume $Is(N#0, 
                Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)))
               && $IsAlloc(N#0, 
                Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)), 
                $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, 
              Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)));
            assume N#0 == let#0_0_0#0#0;
            havoc s#0;
            assume $Is(s#0, Tclass._module.Stream(_module._default.Prepend_Lemma#$T))
               && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Prepend_Lemma#$T), $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_1#0#0, Tclass._module.Stream(_module._default.Prepend_Lemma#$T));
            assume s#0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(252,38)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            x##0 := x#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := N#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Prepend__Lemma_h(_module._default.Prepend_Lemma#$T, _k##0, x##0, M##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(252,43)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(247,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, x#2: Box, M#2: DatatypeType :: 
          $IsBox(x#2, _module._default.Prepend_Lemma#$T)
               && $Is(M#2, 
                Tclass._module.Stream(Tclass._module.Stream(_module._default.Prepend_Lemma#$T)))
               && ORD#Less(_k'#0, _k#0)
             ==> _module.__default.StreamOfNonEmpties_h(_module._default.Prepend_Lemma#$T, 
              $LS($LZ), 
              _k'#0, 
              _module.__default.Prepend(_module._default.Prepend_Lemma#$T, $LS($LZ), x#2, M#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(247,15)"} true;
    }
}



procedure {:_induction M#0} CheckWellformed$$_module.__default.Theorem__Flatten(_module._default.Theorem_Flatten$T: Ty, 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.Theorem_Flatten$T)
         && $IsAllocBox(startMarker#0, _module._default.Theorem_Flatten$T, $Heap));
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction M#0} CheckWellformed$$_module.__default.Theorem__Flatten(_module._default.Theorem_Flatten$T: Ty, M#0: DatatypeType, startMarker#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: Box;
  var ##M#0: DatatypeType;
  var ##M#1: DatatypeType;
  var ##M#2: DatatypeType;
  var ##startMarker#0: Box;
  var ##x#1: Box;
  var ##M#3: DatatypeType;
  var ##M#4: DatatypeType;

    // AddMethodImpl: Theorem_Flatten, CheckWellformed$$_module.__default.Theorem__Flatten
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(256,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(258,48): post-state"} true;
    if (*)
    {
        ##x#0 := startMarker#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0, _module._default.Theorem_Flatten$T, $Heap);
        ##M#0 := M#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)), 
          $Heap);
        assume _module.__default.Prepend#canCall(_module._default.Theorem_Flatten$T, startMarker#0, M#0);
        ##M#1 := _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)), 
          $Heap);
        assume _module.__default.StreamOfNonEmpties#canCall(_module._default.Theorem_Flatten$T, 
          _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0));
        assume _module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, 
          $LS($LZ), 
          _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0));
        ##M#2 := M#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#2, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)), 
          $Heap);
        ##startMarker#0 := startMarker#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##startMarker#0, _module._default.Theorem_Flatten$T, $Heap);
        assume _module.__default.FlattenStartMarker#canCall(_module._default.Theorem_Flatten$T, M#0, startMarker#0);
        ##x#1 := startMarker#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#1, _module._default.Theorem_Flatten$T, $Heap);
        ##M#3 := M#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#3, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)), 
          $Heap);
        assume _module.__default.Prepend#canCall(_module._default.Theorem_Flatten$T, startMarker#0, M#0);
        ##M#4 := _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#4, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)), 
          $Heap);
        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, $LS($LS($LZ)), ##M#4);
        assume _module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, $LS($LZ), ##M#4);
        assume _module.__default.FlattenNonEmpties#canCall(_module._default.Theorem_Flatten$T, 
          _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0));
        assume $Eq#_module.Stream(_module._default.Theorem_Flatten$T, 
          _module._default.Theorem_Flatten$T, 
          $LS($LS($LZ)), 
          _module.__default.FlattenStartMarker(_module._default.Theorem_Flatten$T, M#0, startMarker#0), 
          _module.__default.FlattenNonEmpties(_module._default.Theorem_Flatten$T, 
            _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0)));
    }
    else
    {
        assume _module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, 
            $LS($LZ), 
            _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0))
           ==> $Eq#_module.Stream(_module._default.Theorem_Flatten$T, 
            _module._default.Theorem_Flatten$T, 
            $LS($LS($LZ)), 
            _module.__default.FlattenStartMarker(_module._default.Theorem_Flatten$T, M#0, startMarker#0), 
            _module.__default.FlattenNonEmpties(_module._default.Theorem_Flatten$T, 
              _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0)));
    }
}



procedure {:_induction M#0} Call$$_module.__default.Theorem__Flatten(_module._default.Theorem_Flatten$T: Ty, 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.Theorem_Flatten$T)
         && $IsAllocBox(startMarker#0, _module._default.Theorem_Flatten$T, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Prepend#canCall(_module._default.Theorem_Flatten$T, startMarker#0, M#0)
     && _module.__default.StreamOfNonEmpties#canCall(_module._default.Theorem_Flatten$T, 
      _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0))
     && (_module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, 
        $LS($LZ), 
        _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0))
       ==> $IsA#_module.Stream(_module.__default.FlattenStartMarker(_module._default.Theorem_Flatten$T, M#0, startMarker#0))
         && $IsA#_module.Stream(_module.__default.FlattenNonEmpties(_module._default.Theorem_Flatten$T, 
            _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0)))
         && 
        _module.__default.FlattenStartMarker#canCall(_module._default.Theorem_Flatten$T, M#0, startMarker#0)
         && 
        _module.__default.Prepend#canCall(_module._default.Theorem_Flatten$T, startMarker#0, M#0)
         && _module.__default.FlattenNonEmpties#canCall(_module._default.Theorem_Flatten$T, 
          _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0)));
  ensures _module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, 
      $LS($LZ), 
      _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0))
     ==> $Eq#_module.Stream(_module._default.Theorem_Flatten$T, 
      _module._default.Theorem_Flatten$T, 
      $LS($LS($LZ)), 
      _module.__default.FlattenStartMarker(_module._default.Theorem_Flatten$T, M#0, startMarker#0), 
      _module.__default.FlattenNonEmpties(_module._default.Theorem_Flatten$T, 
        _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LS($LZ)), startMarker#0, M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction M#0} Impl$$_module.__default.Theorem__Flatten(_module._default.Theorem_Flatten$T: Ty, 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.Theorem_Flatten$T)
         && $IsAllocBox(startMarker#0, _module._default.Theorem_Flatten$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Prepend#canCall(_module._default.Theorem_Flatten$T, startMarker#0, M#0)
     && _module.__default.StreamOfNonEmpties#canCall(_module._default.Theorem_Flatten$T, 
      _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0))
     && (_module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, 
        $LS($LZ), 
        _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0))
       ==> $IsA#_module.Stream(_module.__default.FlattenStartMarker(_module._default.Theorem_Flatten$T, M#0, startMarker#0))
         && $IsA#_module.Stream(_module.__default.FlattenNonEmpties(_module._default.Theorem_Flatten$T, 
            _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0)))
         && 
        _module.__default.FlattenStartMarker#canCall(_module._default.Theorem_Flatten$T, M#0, startMarker#0)
         && 
        _module.__default.Prepend#canCall(_module._default.Theorem_Flatten$T, startMarker#0, M#0)
         && _module.__default.FlattenNonEmpties#canCall(_module._default.Theorem_Flatten$T, 
          _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0)));
  ensures _module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, 
      $LS($LZ), 
      _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, M#0))
     ==> $Eq#_module.Stream(_module._default.Theorem_Flatten$T, 
      _module._default.Theorem_Flatten$T, 
      $LS($LS($LZ)), 
      _module.__default.FlattenStartMarker(_module._default.Theorem_Flatten$T, M#0, startMarker#0), 
      _module.__default.FlattenNonEmpties(_module._default.Theorem_Flatten$T, 
        _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LS($LZ)), startMarker#0, M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction M#0} Impl$$_module.__default.Theorem__Flatten(_module._default.Theorem_Flatten$T: Ty, M#0: DatatypeType, startMarker#0: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var x##0: Box;
  var M##0: DatatypeType;
  var prefix##0: DatatypeType;
  var M##1: DatatypeType;
  var startMarker##0: Box;

    // AddMethodImpl: Theorem_Flatten, Impl$$_module.__default.Theorem__Flatten
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(262,0): initial state"} true;
    assume $IsA#_module.Stream(M#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#M0#0: DatatypeType :: 
      $Is($ih#M0#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.Theorem_Flatten$T)))
           && Lit(true)
           && false
         ==> 
        _module.__default.StreamOfNonEmpties(_module._default.Theorem_Flatten$T, 
          $LS($LZ), 
          _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, $ih#M0#0))
         ==> $Eq#_module.Stream(_module._default.Theorem_Flatten$T, 
          _module._default.Theorem_Flatten$T, 
          $LS($LS($LZ)), 
          _module.__default.FlattenStartMarker(_module._default.Theorem_Flatten$T, $ih#M0#0, startMarker#0), 
          _module.__default.FlattenNonEmpties(_module._default.Theorem_Flatten$T, 
            _module.__default.Prepend(_module._default.Theorem_Flatten$T, $LS($LZ), startMarker#0, $ih#M0#0))));
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(263,16)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := startMarker#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    M##0 := M#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Prepend__Lemma(_module._default.Theorem_Flatten$T, x##0, M##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(263,31)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(264,16)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    prefix##0 := Lit(#_module.Stream.Nil());
    assume true;
    // ProcessCallStmt: CheckSubrange
    M##1 := M#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    startMarker##0 := startMarker#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Lemma__Flatten(_module._default.Theorem_Flatten$T, prefix##0, M##1, startMarker##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(264,36)"} true;
}



procedure CheckWellformed$$_module.__default.Lemma__Flatten(_module._default.Lemma_Flatten$T: Ty, 
    prefix#0: DatatypeType
       where $Is(prefix#0, Tclass._module.Stream(_module._default.Lemma_Flatten$T))
         && $IsAlloc(prefix#0, Tclass._module.Stream(_module._default.Lemma_Flatten$T), $Heap)
         && $IsA#_module.Stream(prefix#0), 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.Lemma_Flatten$T)
         && $IsAllocBox(startMarker#0, _module._default.Lemma_Flatten$T, $Heap));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Lemma__Flatten(_module._default.Lemma_Flatten$T: Ty, 
    prefix#0: DatatypeType, 
    M#0: DatatypeType, 
    startMarker#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: Box;
  var ##M#0: DatatypeType;
  var ##M#1: DatatypeType;
  var ##prefix#0: DatatypeType;
  var ##M#2: DatatypeType;
  var ##startMarker#0: Box;
  var ##x#1: Box;
  var ##M#3: DatatypeType;
  var ##prefix#1: DatatypeType;
  var ##M#4: DatatypeType;

    // AddMethodImpl: Lemma_Flatten, CheckWellformed$$_module.__default.Lemma__Flatten
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(267,15): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(269,48): post-state"} true;
    if (*)
    {
        ##x#0 := startMarker#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0, _module._default.Lemma_Flatten$T, $Heap);
        ##M#0 := M#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)), 
          $Heap);
        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten$T, startMarker#0, M#0);
        ##M#1 := _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)), 
          $Heap);
        assume _module.__default.StreamOfNonEmpties#canCall(_module._default.Lemma_Flatten$T, 
          _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0));
        assume _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten$T, 
          $LS($LZ), 
          _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0));
        ##prefix#0 := prefix#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##prefix#0, Tclass._module.Stream(_module._default.Lemma_Flatten$T), $Heap);
        ##M#2 := M#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#2, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)), 
          $Heap);
        ##startMarker#0 := startMarker#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##startMarker#0, _module._default.Lemma_Flatten$T, $Heap);
        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten$T, prefix#0, M#0, startMarker#0);
        ##x#1 := startMarker#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#1, _module._default.Lemma_Flatten$T, $Heap);
        ##M#3 := M#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#3, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)), 
          $Heap);
        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten$T, startMarker#0, M#0);
        ##prefix#1 := prefix#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##prefix#1, Tclass._module.Stream(_module._default.Lemma_Flatten$T), $Heap);
        ##M#4 := _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##M#4, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)), 
          $Heap);
        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten$T, $LS($LS($LZ)), ##M#4);
        assume _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten$T, $LS($LZ), ##M#4);
        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten$T, 
          prefix#0, 
          _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0));
        assume $Eq#_module.Stream(_module._default.Lemma_Flatten$T, 
          _module._default.Lemma_Flatten$T, 
          $LS($LS($LZ)), 
          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten$T, $LS($LZ), prefix#0, M#0, startMarker#0), 
          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten$T, 
            $LS($LZ), 
            prefix#0, 
            _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0)));
    }
    else
    {
        assume _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten$T, 
            $LS($LZ), 
            _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0))
           ==> $Eq#_module.Stream(_module._default.Lemma_Flatten$T, 
            _module._default.Lemma_Flatten$T, 
            $LS($LS($LZ)), 
            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten$T, $LS($LZ), prefix#0, M#0, startMarker#0), 
            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten$T, 
              $LS($LZ), 
              prefix#0, 
              _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0)));
    }
}



procedure Call$$_module.__default.Lemma__Flatten(_module._default.Lemma_Flatten$T: Ty, 
    prefix#0: DatatypeType
       where $Is(prefix#0, Tclass._module.Stream(_module._default.Lemma_Flatten$T))
         && $IsAlloc(prefix#0, Tclass._module.Stream(_module._default.Lemma_Flatten$T), $Heap)
         && $IsA#_module.Stream(prefix#0), 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.Lemma_Flatten$T)
         && $IsAllocBox(startMarker#0, _module._default.Lemma_Flatten$T, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Prepend#canCall(_module._default.Lemma_Flatten$T, startMarker#0, M#0)
     && _module.__default.StreamOfNonEmpties#canCall(_module._default.Lemma_Flatten$T, 
      _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0))
     && (_module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten$T, 
        $LS($LZ), 
        _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0))
       ==> $IsA#_module.Stream(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten$T, $LS($LZ), prefix#0, M#0, startMarker#0))
         && $IsA#_module.Stream(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten$T, 
            $LS($LZ), 
            prefix#0, 
            _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0)))
         && 
        _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten$T, prefix#0, M#0, startMarker#0)
         && 
        _module.__default.Prepend#canCall(_module._default.Lemma_Flatten$T, startMarker#0, M#0)
         && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten$T, 
          prefix#0, 
          _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0)));
  ensures _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten$T, 
      $LS($LZ), 
      _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LZ), startMarker#0, M#0))
     ==> $Eq#_module.Stream(_module._default.Lemma_Flatten$T, 
      _module._default.Lemma_Flatten$T, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten$T, $LS($LS($LZ)), prefix#0, M#0, startMarker#0), 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten$T, 
        $LS($LS($LZ)), 
        prefix#0, 
        _module.__default.Prepend(_module._default.Lemma_Flatten$T, $LS($LS($LZ)), startMarker#0, M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, prefix#1, M#1} CoCall$$_module.__default.Lemma__Flatten_h(_module._default.Lemma_Flatten#$T: Ty, 
    _k#0: Box, 
    prefix#1: DatatypeType
       where $Is(prefix#1, Tclass._module.Stream(_module._default.Lemma_Flatten#$T))
         && $IsAlloc(prefix#1, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap)
         && $IsA#_module.Stream(prefix#1), 
    M#1: DatatypeType
       where $Is(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)))
         && $IsAlloc(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
          $Heap)
         && $IsA#_module.Stream(M#1), 
    startMarker#1: Box
       where $IsBox(startMarker#1, _module._default.Lemma_Flatten#$T)
         && $IsAllocBox(startMarker#1, _module._default.Lemma_Flatten#$T, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
     && _module.__default.StreamOfNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
     && (_module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, 
        $LS($LZ), 
        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
       ==> _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1)
         && 
        _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
         && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
          prefix#1, 
          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)));
  free ensures _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, 
      $LS($LZ), 
      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
     ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
      _module._default.Lemma_Flatten#$T, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
        $LS($LZ), 
        prefix#1, 
        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, prefix#1, M#1} Impl$$_module.__default.Lemma__Flatten_h(_module._default.Lemma_Flatten#$T: Ty, 
    _k#0: Box, 
    prefix#1: DatatypeType
       where $Is(prefix#1, Tclass._module.Stream(_module._default.Lemma_Flatten#$T))
         && $IsAlloc(prefix#1, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap)
         && $IsA#_module.Stream(prefix#1), 
    M#1: DatatypeType
       where $Is(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)))
         && $IsAlloc(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
          $Heap)
         && $IsA#_module.Stream(M#1), 
    startMarker#1: Box
       where $IsBox(startMarker#1, _module._default.Lemma_Flatten#$T)
         && $IsAllocBox(startMarker#1, _module._default.Lemma_Flatten#$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
     && _module.__default.StreamOfNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
     && (_module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, 
        $LS($LZ), 
        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
       ==> _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1)
         && 
        _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
         && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
          prefix#1, 
          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)));
  ensures _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, 
      $LS($LZ), 
      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
     ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
        _module._default.Lemma_Flatten#$T, 
        _k#0, 
        $LS($LS($LZ)), 
        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
          $LS($LZ), 
          prefix#1, 
          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
       || (0 < ORD#Offset(_k#0)
         ==> 
        _module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
         ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
            $LS($LS($LZ)), 
            prefix#1, 
            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))));
  ensures _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, 
      $LS($LZ), 
      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
     ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
        _module._default.Lemma_Flatten#$T, 
        _k#0, 
        $LS($LS($LZ)), 
        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
          $LS($LZ), 
          prefix#1, 
          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
       || (0 < ORD#Offset(_k#0)
         ==> 
        _module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
         ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
              $LS($LS($LZ)), 
              prefix#1, 
              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
           && 
          _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
             == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                $LS($LS($LZ)), 
                prefix#1, 
                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
           && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
            _module._default.Lemma_Flatten#$T, 
            ORD#Minus(_k#0, ORD#FromNat(1)), 
            $LS($LS($LZ)), 
            _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1)), 
            _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                $LS($LS($LZ)), 
                prefix#1, 
                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))));
  ensures _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, 
      $LS($LZ), 
      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
     ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
        _module._default.Lemma_Flatten#$T, 
        _k#0, 
        $LS($LS($LZ)), 
        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
          $LS($LZ), 
          prefix#1, 
          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
       || 
      (0 < ORD#Offset(_k#0)
         ==> (_module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
             ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                $LS($LS($LZ)), 
                prefix#1, 
                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))))
           && (_module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
             ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                  $LS($LS($LZ)), 
                  prefix#1, 
                  _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
               && 
              _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
                 == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                    $LS($LS($LZ)), 
                    prefix#1, 
                    _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
               && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                _module._default.Lemma_Flatten#$T, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                $LS($LS($LZ)), 
                _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1)), 
                _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                    $LS($LS($LZ)), 
                    prefix#1, 
                    _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))))))
       || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
         ==> $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
          _module._default.Lemma_Flatten#$T, 
          $LS($LS($LZ)), 
          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
            $LS($LZ), 
            prefix#1, 
            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, prefix#1, M#1} Impl$$_module.__default.Lemma__Flatten_h(_module._default.Lemma_Flatten#$T: Ty, 
    _k#0: Box, 
    prefix#1: DatatypeType, 
    M#1: DatatypeType, 
    startMarker#1: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var x##0: Box;
  var M##0: DatatypeType;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tl#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var hd#0: Box;
  var let#0_0_1#0#0: Box;
  var _k##0: Box;
  var prefix##0: DatatypeType;
  var M##1: DatatypeType;
  var startMarker##0: Box;
  var _mcc#2#0: DatatypeType;
  var _mcc#3#0: DatatypeType;
  var N#0: DatatypeType;
  var let#0_1_0_0#0#0: DatatypeType;
  var s#0: DatatypeType;
  var let#0_1_0_1#0#0: DatatypeType;
  var _k##1: Box;
  var prefix##1: DatatypeType;
  var M##2: DatatypeType;
  var startMarker##1: Box;
  var ##prefix#2: DatatypeType;
  var ##M#5: DatatypeType;
  var ##startMarker#1: Box;
  var ##prefix#3: DatatypeType;
  var ##M#6: DatatypeType;
  var ##startMarker#2: Box;
  var ##prefix#4: DatatypeType;
  var ##M#7: DatatypeType;
  var ##startMarker#3: Box;
  var ##x#2: Box;
  var ##M#8: DatatypeType;
  var ##prefix#5: DatatypeType;
  var ##M#9: DatatypeType;
  var ##x#3: Box;
  var ##M#10: DatatypeType;
  var ##prefix#6: DatatypeType;
  var ##M#11: DatatypeType;
  var ##x#4: Box;
  var ##M#12: DatatypeType;
  var ##prefix#7: DatatypeType;
  var ##M#13: DatatypeType;
  var ##x#5: Box;
  var ##M#14: DatatypeType;
  var ##prefix#8: DatatypeType;
  var ##M#15: DatatypeType;
  var ##x#6: Box;
  var ##M#16: DatatypeType;
  var ##prefix#9: DatatypeType;
  var ##M#17: DatatypeType;
  var ##x#7: Box;
  var ##M#18: DatatypeType;
  var ##prefix#10: DatatypeType;
  var ##M#19: DatatypeType;
  var ##x#8: Box;
  var ##M#20: DatatypeType;
  var ##prefix#11: DatatypeType;
  var ##M#21: DatatypeType;
  var ##x#9: Box;
  var ##M#22: DatatypeType;
  var ##prefix#12: DatatypeType;
  var ##M#23: DatatypeType;
  var ##x#10: Box;
  var ##M#24: DatatypeType;
  var ##prefix#13: DatatypeType;
  var ##M#25: DatatypeType;
  var _k##2: Box;
  var prefix##2: DatatypeType;
  var M##3: DatatypeType;
  var startMarker##2: Box;
  var ##prefix#14: DatatypeType;
  var ##M#26: DatatypeType;
  var ##startMarker#4: Box;
  var ##x#11: Box;
  var ##M#27: DatatypeType;
  var ##prefix#15: DatatypeType;
  var ##M#28: DatatypeType;
  var ##prefix#16: DatatypeType;
  var ##M#29: DatatypeType;
  var ##startMarker#5: Box;
  var ##x#12: Box;
  var ##M#30: DatatypeType;
  var ##prefix#17: DatatypeType;
  var ##M#31: DatatypeType;
  var ##prefix#18: DatatypeType;
  var ##M#32: DatatypeType;
  var ##startMarker#6: Box;
  var ##x#13: Box;
  var ##M#33: DatatypeType;
  var ##prefix#19: DatatypeType;
  var ##M#34: DatatypeType;
  var ##prefix#20: DatatypeType;
  var ##M#35: DatatypeType;
  var ##startMarker#7: Box;
  var ##x#14: Box;
  var ##M#36: DatatypeType;
  var ##prefix#21: DatatypeType;
  var ##M#37: DatatypeType;
  var ##prefix#22: DatatypeType;
  var ##M#38: DatatypeType;
  var ##startMarker#8: Box;
  var ##x#15: Box;
  var ##M#39: DatatypeType;
  var ##prefix#23: DatatypeType;
  var ##M#40: DatatypeType;
  var ##x#16: Box;
  var ##M#41: DatatypeType;
  var ##prefix#24: DatatypeType;
  var ##M#42: DatatypeType;
  var ##x#17: Box;
  var ##M#43: DatatypeType;
  var ##prefix#25: DatatypeType;
  var ##M#44: DatatypeType;
  var ##prefix#26: DatatypeType;
  var ##M#45: DatatypeType;
  var ##startMarker#9: Box;
  var ##x#18: Box;
  var ##M#46: DatatypeType;
  var ##prefix#27: DatatypeType;
  var ##M#47: DatatypeType;
  var ##prefix#28: DatatypeType;
  var ##M#48: DatatypeType;
  var ##startMarker#10: Box;
  var ##x#19: Box;
  var ##M#49: DatatypeType;
  var ##prefix#29: DatatypeType;
  var ##M#50: DatatypeType;
  var ##prefix#30: DatatypeType;
  var ##M#51: DatatypeType;
  var ##startMarker#11: Box;
  var ##prefix#31: DatatypeType;
  var ##M#52: DatatypeType;
  var ##startMarker#12: Box;
  var ##prefix#32: DatatypeType;
  var ##M#53: DatatypeType;
  var ##startMarker#13: Box;
  var ##x#20: Box;
  var ##M#54: DatatypeType;
  var ##prefix#33: DatatypeType;
  var ##M#55: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Lemma_Flatten#, Impl$$_module.__default.Lemma__Flatten_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(267,15): initial state"} true;
    assume $IsA#_module.Stream(prefix#1);
    assume $IsA#_module.Stream(M#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#prefix0#0: DatatypeType, $ih#M0#0: DatatypeType :: 
      $Is($ih#prefix0#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T))
           && $Is($ih#M0#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> 
        _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, 
          $LS($LZ), 
          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, $ih#M0#0))
         ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
          _module._default.Lemma_Flatten#$T, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, 
            $LS($LZ), 
            $ih#prefix0#0, 
            $ih#M0#0, 
            startMarker#1), 
          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
            $LS($LZ), 
            $ih#prefix0#0, 
            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, $ih#M0#0))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(273,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(274,16)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        x##0 := startMarker#1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        M##0 := M#1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Prepend__Lemma(_module._default.Lemma_Flatten#$T, x##0, M##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(274,31)"} true;
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (prefix#1 == #_module.Stream.Nil())
        {
            assume true;
            havoc _mcc#2#0, _mcc#3#0;
            if (M#1 == #_module.Stream.Nil())
            {
            }
            else if (M#1 == #_module.Stream.Cons($Box(_mcc#2#0), _mcc#3#0))
            {
                assume $Is(_mcc#2#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T))
                   && $IsAlloc(_mcc#2#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                assume $Is(_mcc#3#0, 
                    Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)))
                   && $IsAlloc(_mcc#3#0, 
                    Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                    $Heap);
                havoc N#0;
                assume $Is(N#0, 
                    Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)))
                   && $IsAlloc(N#0, 
                    Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                    $Heap);
                assume let#0_1_0_0#0#0 == _mcc#3#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#0_1_0_0#0#0, 
                  Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)));
                assume N#0 == let#0_1_0_0#0#0;
                havoc s#0;
                assume $Is(s#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T))
                   && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                assume let#0_1_0_1#0#0 == _mcc#2#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#0_1_0_1#0#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T));
                assume s#0 == let#0_1_0_1#0#0;
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(282,11)
                if (*)
                {
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(284,26)
                    // TrCallStmt: Before ProcessCallStmt
                    assert ORD#IsNat(Lit(ORD#FromNat(1)));
                    assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    _k##1 := ORD#Minus(_k#0, ORD#FromNat(1));
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    prefix##1 := s#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    M##2 := N#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    startMarker##1 := startMarker#1;
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call CoCall$$_module.__default.Lemma__Flatten_h(_module._default.Lemma_Flatten#$T, _k##1, prefix##1, M##2, startMarker##1);
                    // TrCallStmt: After ProcessCallStmt
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(284,44)"} true;
                }
                else
                {
                    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(290,13)
                    // Assume Fuel Constant
                    if (*)
                    {
                        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(290,13)
                        ##prefix#4 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#4, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#7 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#7, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#3 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#3, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1);
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(290,13)
                        ##prefix#2 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#2, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#5 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#5, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#1 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#1, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1);
                        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(290,13)
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(290,13)
                        ##prefix#3 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#3, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#6 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#6, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#2 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#2, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(290,13)
                        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)));
                        assume false;
                    }

                    assume $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                      _module._default.Lemma_Flatten#$T, 
                      $LS($LS($LZ)), 
                      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
                      #_module.Stream.Cons(startMarker#1, 
                        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)));
                    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                    // Assume Fuel Constant
                    if (*)
                    {
                        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        ##x#10 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#10, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#24 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#24, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1);
                        ##prefix#13 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#13, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#25 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#25, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#25);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        ##x#8 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#8, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#20 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#20, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1);
                        ##prefix#11 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#11, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#21 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#21, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#21);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        ##x#9 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#9, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#22 := #_module.Stream.Cons($Box(s#0), N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#22, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, 
                          startMarker#1, 
                          #_module.Stream.Cons($Box(s#0), N#0));
                        ##prefix#12 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#12, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#23 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, 
                          $LS($LZ), 
                          startMarker#1, 
                          #_module.Stream.Cons($Box(s#0), N#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#23, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#23);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, 
                            $LS($LZ), 
                            startMarker#1, 
                            #_module.Stream.Cons($Box(s#0), N#0)));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, 
                            startMarker#1, 
                            #_module.Stream.Cons($Box(s#0), N#0))
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              startMarker#1, 
                              #_module.Stream.Cons($Box(s#0), N#0)));
                        // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LS($LZ)), 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LS($LZ)), 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, 
                              $LS($LS($LZ)), 
                              startMarker#1, 
                              #_module.Stream.Cons($Box(s#0), N#0))));
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        ##x#6 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#6, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#16 := #_module.Stream.Cons($Box(s#0), N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#16, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, 
                          startMarker#1, 
                          #_module.Stream.Cons($Box(s#0), N#0));
                        ##prefix#9 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#9, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#17 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, 
                          $LS($LZ), 
                          startMarker#1, 
                          #_module.Stream.Cons($Box(s#0), N#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#17, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#17);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, 
                            $LS($LZ), 
                            startMarker#1, 
                            #_module.Stream.Cons($Box(s#0), N#0)));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, 
                            startMarker#1, 
                            #_module.Stream.Cons($Box(s#0), N#0))
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              startMarker#1, 
                              #_module.Stream.Cons($Box(s#0), N#0)));
                        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        ##x#7 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#7, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#18 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#18, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#10 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#10, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#19 := #_module.Stream.Cons($Box(#_module.Stream.Cons(startMarker#1, s#0)), 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#19, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#19);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          #_module.Stream.Cons($Box(#_module.Stream.Cons(startMarker#1, s#0)), 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            #_module.Stream.Cons($Box(#_module.Stream.Cons(startMarker#1, s#0)), 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)));
                        // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LS($LZ)), 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, 
                              $LS($LS($LZ)), 
                              startMarker#1, 
                              #_module.Stream.Cons($Box(s#0), N#0))), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LS($LZ)), 
                            prefix#1, 
                            #_module.Stream.Cons($Box(#_module.Stream.Cons(startMarker#1, s#0)), 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))));
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        ##x#4 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#4, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#12 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#12, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#7 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#7, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#13 := #_module.Stream.Cons($Box(#_module.Stream.Cons(startMarker#1, s#0)), 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#13, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#13);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          #_module.Stream.Cons($Box(#_module.Stream.Cons(startMarker#1, s#0)), 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            #_module.Stream.Cons($Box(#_module.Stream.Cons(startMarker#1, s#0)), 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)));
                        // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        assert _module.Stream.Cons_q(#_module.Stream.Cons(startMarker#1, s#0));
                        assert _module.Stream.Cons_q(#_module.Stream.Cons(startMarker#1, s#0));
                        ##x#5 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#5, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#14 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#14, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#8 := _module.Stream.tail(#_module.Stream.Cons(startMarker#1, s#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#8, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#15 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#15, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#15);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          _module.Stream.tail(#_module.Stream.Cons(startMarker#1, s#0)), 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            _module.Stream.tail(#_module.Stream.Cons(startMarker#1, s#0)), 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LS($LZ)), 
                            prefix#1, 
                            #_module.Stream.Cons($Box(#_module.Stream.Cons(startMarker#1, s#0)), 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))), 
                          #_module.Stream.Cons(_module.Stream.head(#_module.Stream.Cons(startMarker#1, s#0)), 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LS($LZ)), 
                              _module.Stream.tail(#_module.Stream.Cons(startMarker#1, s#0)), 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))));
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        assume _module.Stream.Cons_q(#_module.Stream.Cons(startMarker#1, s#0));
                        assume _module.Stream.Cons_q(#_module.Stream.Cons(startMarker#1, s#0));
                        ##x#2 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#2, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#8 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#8, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#5 := _module.Stream.tail(#_module.Stream.Cons(startMarker#1, s#0));
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#5, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#9 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#9, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#9);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          _module.Stream.tail(#_module.Stream.Cons(startMarker#1, s#0)), 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            _module.Stream.tail(#_module.Stream.Cons(startMarker#1, s#0)), 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        ##x#3 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#3, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#10 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#10, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#6 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#6, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#11 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#11, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#11);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          s#0, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            s#0, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(296,13)
                        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          #_module.Stream.Cons(_module.Stream.head(#_module.Stream.Cons(startMarker#1, s#0)), 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LS($LZ)), 
                              _module.Stream.tail(#_module.Stream.Cons(startMarker#1, s#0)), 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LS($LZ)), 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))));
                        assume false;
                    }

                    assume $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                      _module._default.Lemma_Flatten#$T, 
                      $LS($LS($LZ)), 
                      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                        $LS($LZ), 
                        prefix#1, 
                        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)), 
                      #_module.Stream.Cons(startMarker#1, 
                        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                          $LS($LZ), 
                          s#0, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0))));
                    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                    // Assume Fuel Constant
                    if (*)
                    {
                        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assume true;
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        ##prefix#28 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#28, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#48 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#48, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#10 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#10, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        ##x#19 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#19, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#49 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#49, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1);
                        ##prefix#29 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#29, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#50 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#50, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#50);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1)
                           && 
                          _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assume $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          _k#0, 
                          $LS($LS($LZ)), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LZ), 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)));
                        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(312,17)
                        ##prefix#30 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#30, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#51 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#51, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#11 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#11, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1);
                        ##prefix#31 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#31, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#52 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#52, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#12 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#12, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        assume $IsA#_module.Stream(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1))
                           && 
                          _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1)
                           && _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)));
                        assume $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)));
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        ##prefix#32 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#32, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#53 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#53, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#13 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#13, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1);
                        ##x#20 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#20, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#54 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#54, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1);
                        ##prefix#33 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#33, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#55 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#55, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#55);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, prefix#1, M#1, startMarker#1)
                           && 
                          _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            _k#0, 
                            $LS($LS($LZ)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              prefix#1, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              _k#0, 
                              $LS($LS($LZ)), 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                prefix#1, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                             || (0 < ORD#Offset(_k#0)
                               ==> 
                              _module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
                               ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                  $LS($LS($LZ)), 
                                  prefix#1, 
                                  _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))));
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            _k#0, 
                            $LS($LS($LZ)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              prefix#1, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              _k#0, 
                              $LS($LS($LZ)), 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                prefix#1, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                             || (0 < ORD#Offset(_k#0)
                               ==> 
                              _module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
                               ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                    $LS($LS($LZ)), 
                                    prefix#1, 
                                    _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
                                 && 
                                _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
                                   == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      prefix#1, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
                                 && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                  _module._default.Lemma_Flatten#$T, 
                                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                                  $LS($LS($LZ)), 
                                  _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1)), 
                                  _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      prefix#1, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))));
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            _k#0, 
                            $LS($LS($LZ)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              prefix#1, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              _k#0, 
                              $LS($LS($LZ)), 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                prefix#1, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                             || 
                            (0 < ORD#Offset(_k#0)
                               ==> (_module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
                                   ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      prefix#1, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))))
                                 && (_module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
                                   ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                        $LS($LS($LZ)), 
                                        prefix#1, 
                                        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
                                     && 
                                    _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1))
                                       == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                          $LS($LS($LZ)), 
                                          prefix#1, 
                                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
                                     && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                      _module._default.Lemma_Flatten#$T, 
                                      ORD#Minus(_k#0, ORD#FromNat(1)), 
                                      $LS($LS($LZ)), 
                                      _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), prefix#1, M#1, startMarker#1)), 
                                      _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                          $LS($LS($LZ)), 
                                          prefix#1, 
                                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))))))
                             || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
                               ==> $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                _module._default.Lemma_Flatten#$T, 
                                $LS($LS($LZ)), 
                                _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
                                _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                  $LS($LZ), 
                                  prefix#1, 
                                  _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))));
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        ##prefix#22 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#22, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#38 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#38, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#8 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#8, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        ##x#15 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#15, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#39 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#39, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#23 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#23, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#40 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#40, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#40);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          s#0, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1)
                           && 
                          _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            s#0, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assume $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          _k#0, 
                          $LS($LS($LZ)), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0))));
                        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(315,17)
                        ##x#16 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#16, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#41 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#41, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1);
                        ##prefix#24 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#24, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#42 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#42, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#42);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        ##x#17 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#17, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#43 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#43, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#25 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#25, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#44 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#44, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#44);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          s#0, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assume $IsA#_module.Stream(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              prefix#1, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                           && 
                          _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))
                           && 
                          _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            s#0, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LS($LZ)), 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LS($LZ)), 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))));
                        assume $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LZ), 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)), 
                          #_module.Stream.Cons(startMarker#1, 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0))));
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        ##prefix#26 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#26, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#45 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#45, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#9 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#9, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        ##x#18 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#18, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#46 := M#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#46, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1);
                        ##prefix#27 := prefix#1;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#27, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#47 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#47, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#47);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1)
                           && 
                          _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, M#1)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            prefix#1, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1));
                        // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            _k#0, 
                            $LS($LS($LZ)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0))))
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              _k#0, 
                              $LS($LS($LZ)), 
                              #_module.Stream.Cons(startMarker#1, 
                                _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                prefix#1, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                             || (0 < ORD#Offset(_k#0)
                               ==> 
                              _module.Stream.Nil_q(#_module.Stream.Cons(startMarker#1, 
                                  _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)))
                               ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                  $LS($LS($LZ)), 
                                  prefix#1, 
                                  _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))));
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            _k#0, 
                            $LS($LS($LZ)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0))))
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              _k#0, 
                              $LS($LS($LZ)), 
                              #_module.Stream.Cons(startMarker#1, 
                                _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                prefix#1, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                             || (0 < ORD#Offset(_k#0)
                               ==> 
                              _module.Stream.Cons_q(#_module.Stream.Cons(startMarker#1, 
                                  _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)))
                               ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                    $LS($LS($LZ)), 
                                    prefix#1, 
                                    _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
                                 && 
                                _module.Stream.head(#_module.Stream.Cons(startMarker#1, 
                                      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)))
                                   == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      prefix#1, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
                                 && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                  _module._default.Lemma_Flatten#$T, 
                                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                                  $LS($LS($LZ)), 
                                  _module.Stream.tail(#_module.Stream.Cons(startMarker#1, 
                                      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))), 
                                  _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      prefix#1, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))));
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            _k#0, 
                            $LS($LS($LZ)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0))))
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              _k#0, 
                              $LS($LS($LZ)), 
                              #_module.Stream.Cons(startMarker#1, 
                                _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                prefix#1, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)))
                             || 
                            (0 < ORD#Offset(_k#0)
                               ==> (_module.Stream.Nil_q(#_module.Stream.Cons(startMarker#1, 
                                      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)))
                                   ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      prefix#1, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))))
                                 && (_module.Stream.Cons_q(#_module.Stream.Cons(startMarker#1, 
                                      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)))
                                   ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                        $LS($LS($LZ)), 
                                        prefix#1, 
                                        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
                                     && 
                                    _module.Stream.head(#_module.Stream.Cons(startMarker#1, 
                                          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)))
                                       == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                          $LS($LS($LZ)), 
                                          prefix#1, 
                                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1)))
                                     && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                      _module._default.Lemma_Flatten#$T, 
                                      ORD#Minus(_k#0, ORD#FromNat(1)), 
                                      $LS($LS($LZ)), 
                                      _module.Stream.tail(#_module.Stream.Cons(startMarker#1, 
                                          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))), 
                                      _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                          $LS($LS($LZ)), 
                                          prefix#1, 
                                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, M#1))))))
                             || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
                               ==> $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                _module._default.Lemma_Flatten#$T, 
                                $LS($LS($LZ)), 
                                #_module.Stream.Cons(startMarker#1, 
                                  _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1)), 
                                _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                  $LS($LZ), 
                                  prefix#1, 
                                  _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1))));
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        ##prefix#18 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#18, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#32 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#32, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#6 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#6, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        ##x#13 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#13, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#33 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#33, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#19 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#19, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#34 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#34, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#34);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          s#0, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1)
                           && 
                          _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            s#0, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        if (startMarker#1 == startMarker#1)
                        {
                            assert ORD#IsNat(Lit(ORD#FromNat(1)));
                            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                            ##prefix#20 := s#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##prefix#20, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                            ##M#35 := N#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##M#35, 
                              Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                              $Heap);
                            ##startMarker#7 := startMarker#1;
                            // assume allocatedness for argument to function
                            assume $IsAllocBox(##startMarker#7, _module._default.Lemma_Flatten#$T, $Heap);
                            assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                            ##x#14 := startMarker#1;
                            // assume allocatedness for argument to function
                            assume $IsAllocBox(##x#14, _module._default.Lemma_Flatten#$T, $Heap);
                            ##M#36 := N#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##M#36, 
                              Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                              $Heap);
                            assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                            ##prefix#21 := s#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##prefix#21, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                            ##M#37 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##M#37, 
                              Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                              $Heap);
                            assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#37);
                            assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        }

                        assume startMarker#1 == startMarker#1
                           ==> _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1)
                             && 
                            _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                             && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            _k#0, 
                            $LS($LS($LZ)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)), 
                            #_module.Stream.Cons(startMarker#1, 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LS($LZ)), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))))
                           == (startMarker#1 == startMarker#1
                             && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              ORD#Minus(_k#0, ORD#FromNat(1)), 
                              $LS($LS($LZ)), 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LS($LZ)), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))));
                        assume false;
                    }
                    else if (*)
                    {
                        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assume true;
                        // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assume true;
                        // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(320,30)
                        // TrCallStmt: Before ProcessCallStmt
                        assert ORD#IsNat(Lit(ORD#FromNat(1)));
                        assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                        assume true;
                        // ProcessCallStmt: CheckSubrange
                        _k##2 := ORD#Minus(_k#0, ORD#FromNat(1));
                        assume true;
                        // ProcessCallStmt: CheckSubrange
                        prefix##2 := s#0;
                        assume true;
                        // ProcessCallStmt: CheckSubrange
                        M##3 := N#0;
                        assume true;
                        // ProcessCallStmt: CheckSubrange
                        startMarker##2 := startMarker#1;
                        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        // ProcessCallStmt: Make the call
                        call CoCall$$_module.__default.Lemma__Flatten_h(_module._default.Lemma_Flatten#$T, _k##2, prefix##2, M##3, startMarker##2);
                        // TrCallStmt: After ProcessCallStmt
                        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(320,48)"} true;
                        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(322,17)
                        assert ORD#IsNat(Lit(ORD#FromNat(1)));
                        assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                        ##prefix#14 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#14, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#26 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#26, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        ##startMarker#4 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##startMarker#4, _module._default.Lemma_Flatten#$T, $Heap);
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                        ##x#11 := startMarker#1;
                        // assume allocatedness for argument to function
                        assume $IsAllocBox(##x#11, _module._default.Lemma_Flatten#$T, $Heap);
                        ##M#27 := N#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#27, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                        ##prefix#15 := s#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##prefix#15, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                        ##M#28 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##M#28, 
                          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                          $Heap);
                        assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#28);
                        assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                          s#0, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1)
                           && 
                          _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                           && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                            s#0, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $LS($LS($LZ)), 
                            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)))
                           || (0 < ORD#Offset(ORD#Minus(_k#0, ORD#FromNat(1)))
                             ==> 
                            _module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                             ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LS($LZ)), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))));
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $LS($LS($LZ)), 
                            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)))
                           || (0 < ORD#Offset(ORD#Minus(_k#0, ORD#FromNat(1)))
                             ==> 
                            _module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                             ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                  $LS($LS($LZ)), 
                                  s#0, 
                                  _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))
                               && 
                              _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                                 == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                    $LS($LS($LZ)), 
                                    s#0, 
                                    _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))
                               && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                _module._default.Lemma_Flatten#$T, 
                                ORD#Minus(ORD#Minus(_k#0, ORD#FromNat(1)), ORD#FromNat(1)), 
                                $LS($LS($LZ)), 
                                _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)), 
                                _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                    $LS($LS($LZ)), 
                                    s#0, 
                                    _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))));
                        assert {:subsumption 0} $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                            _module._default.Lemma_Flatten#$T, 
                            ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $LS($LS($LZ)), 
                            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                              $LS($LZ), 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)))
                           || 
                          (0 < ORD#Offset(ORD#Minus(_k#0, ORD#FromNat(1)))
                             ==> (_module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                                 ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                    $LS($LS($LZ)), 
                                    s#0, 
                                    _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))))
                               && (_module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                                 ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      s#0, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))
                                   && 
                                  _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                                     == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                        $LS($LS($LZ)), 
                                        s#0, 
                                        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))
                                   && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                    _module._default.Lemma_Flatten#$T, 
                                    ORD#Minus(ORD#Minus(_k#0, ORD#FromNat(1)), ORD#FromNat(1)), 
                                    $LS($LS($LZ)), 
                                    _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)), 
                                    _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                        $LS($LS($LZ)), 
                                        s#0, 
                                        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))))))
                           || (ORD#Minus(_k#0, ORD#FromNat(1)) != ORD#FromNat(0)
                               && ORD#IsLimit(ORD#Minus(_k#0, ORD#FromNat(1)))
                             ==> $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              $LS($LS($LZ)), 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0))));
                        assume $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                          _module._default.Lemma_Flatten#$T, 
                          ORD#Minus(_k#0, ORD#FromNat(1)), 
                          $LS($LS($LZ)), 
                          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                            $LS($LZ), 
                            s#0, 
                            _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)));
                        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        if (startMarker#1 == startMarker#1)
                        {
                            assert ORD#IsNat(Lit(ORD#FromNat(1)));
                            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                            ##prefix#16 := s#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##prefix#16, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                            ##M#29 := N#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##M#29, 
                              Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                              $Heap);
                            ##startMarker#5 := startMarker#1;
                            // assume allocatedness for argument to function
                            assume $IsAllocBox(##startMarker#5, _module._default.Lemma_Flatten#$T, $Heap);
                            assume _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1);
                            ##x#12 := startMarker#1;
                            // assume allocatedness for argument to function
                            assume $IsAllocBox(##x#12, _module._default.Lemma_Flatten#$T, $Heap);
                            ##M#30 := N#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##M#30, 
                              Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                              $Heap);
                            assume _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0);
                            ##prefix#17 := s#0;
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##prefix#17, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
                            ##M#31 := _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0);
                            // assume allocatedness for argument to function
                            assume $IsAlloc(##M#31, 
                              Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)), 
                              $Heap);
                            assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), ##M#31);
                            assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        }

                        assume startMarker#1 == startMarker#1
                           ==> _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_Flatten#$T, s#0, N#0, startMarker#1)
                             && 
                            _module.__default.Prepend#canCall(_module._default.Lemma_Flatten#$T, startMarker#1, N#0)
                             && _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_Flatten#$T, 
                              s#0, 
                              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0));
                        // ----- assert line3 <== line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(309,13)
                        assert {:subsumption 0} Lit(true) ==> startMarker#1 == startMarker#1;
                        assert {:subsumption 0} Lit(true)
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              ORD#Minus(_k#0, ORD#FromNat(1)), 
                              $LS($LS($LZ)), 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)))
                             || (0 < ORD#Offset(ORD#Minus(_k#0, ORD#FromNat(1)))
                               ==> 
                              _module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                               ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                  $LS($LS($LZ)), 
                                  s#0, 
                                  _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))));
                        assert {:subsumption 0} Lit(true)
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              ORD#Minus(_k#0, ORD#FromNat(1)), 
                              $LS($LS($LZ)), 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)))
                             || (0 < ORD#Offset(ORD#Minus(_k#0, ORD#FromNat(1)))
                               ==> 
                              _module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                               ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                    $LS($LS($LZ)), 
                                    s#0, 
                                    _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))
                                 && 
                                _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                                   == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      s#0, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))
                                 && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                  _module._default.Lemma_Flatten#$T, 
                                  ORD#Minus(ORD#Minus(_k#0, ORD#FromNat(1)), ORD#FromNat(1)), 
                                  $LS($LS($LZ)), 
                                  _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)), 
                                  _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      s#0, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))));
                        assert {:subsumption 0} Lit(true)
                           ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                              _module._default.Lemma_Flatten#$T, 
                              ORD#Minus(_k#0, ORD#FromNat(1)), 
                              $LS($LS($LZ)), 
                              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                $LS($LZ), 
                                s#0, 
                                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0)))
                             || 
                            (0 < ORD#Offset(ORD#Minus(_k#0, ORD#FromNat(1)))
                               ==> (_module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                                   ==> _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                      $LS($LS($LZ)), 
                                      s#0, 
                                      _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))))
                                 && (_module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                                   ==> _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                        $LS($LS($LZ)), 
                                        s#0, 
                                        _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))
                                     && 
                                    _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1))
                                       == _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                          $LS($LS($LZ)), 
                                          s#0, 
                                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0)))
                                     && $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                      _module._default.Lemma_Flatten#$T, 
                                      ORD#Minus(ORD#Minus(_k#0, ORD#FromNat(1)), ORD#FromNat(1)), 
                                      $LS($LS($LZ)), 
                                      _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), s#0, N#0, startMarker#1)), 
                                      _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                          $LS($LS($LZ)), 
                                          s#0, 
                                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LS($LZ)), startMarker#1, N#0))))))
                             || (ORD#Minus(_k#0, ORD#FromNat(1)) != ORD#FromNat(0)
                                 && ORD#IsLimit(ORD#Minus(_k#0, ORD#FromNat(1)))
                               ==> $Eq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                                _module._default.Lemma_Flatten#$T, 
                                $LS($LS($LZ)), 
                                _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), s#0, N#0, startMarker#1), 
                                _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                                  $LS($LZ), 
                                  s#0, 
                                  _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, N#0))));
                        assume false;
                    }

                    assume true
                       ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
                        _module._default.Lemma_Flatten#$T, 
                        _k#0, 
                        $LS($LS($LZ)), 
                        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#1, M#1, startMarker#1), 
                        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                          $LS($LZ), 
                          prefix#1, 
                          _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#1, M#1)));
                }
            }
            else
            {
                assume false;
            }
        }
        else if (prefix#1 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.Lemma_Flatten#$T)
               && $IsAllocBox(_mcc#0#0, _module._default.Lemma_Flatten#$T, $Heap);
            assume $Is(_mcc#1#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
            havoc tl#0;
            assume $Is(tl#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T))
               && $IsAlloc(tl#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(_module._default.Lemma_Flatten#$T));
            assume tl#0 == let#0_0_0#0#0;
            havoc hd#0;
            assume $IsBox(hd#0, _module._default.Lemma_Flatten#$T)
               && $IsAllocBox(hd#0, _module._default.Lemma_Flatten#$T, $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0_0_1#0#0, _module._default.Lemma_Flatten#$T);
            assume hd#0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(277,18)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            prefix##0 := tl#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##1 := M#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            startMarker##0 := startMarker#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Lemma__Flatten_h(_module._default.Lemma_Flatten#$T, _k##0, prefix##0, M##1, startMarker##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(277,37)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(267,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, prefix#2: DatatypeType, M#2: DatatypeType, startMarker#2: Box :: 
          $Is(prefix#2, Tclass._module.Stream(_module._default.Lemma_Flatten#$T))
               && $Is(M#2, 
                Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_Flatten#$T)))
               && $IsBox(startMarker#2, _module._default.Lemma_Flatten#$T)
               && ORD#Less(_k'#0, _k#0)
             ==> 
            _module.__default.StreamOfNonEmpties(_module._default.Lemma_Flatten#$T, 
              $LS($LZ), 
              _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#2, M#2))
             ==> $PrefixEq#_module.Stream(_module._default.Lemma_Flatten#$T, 
              _module._default.Lemma_Flatten#$T, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_Flatten#$T, $LS($LZ), prefix#2, M#2, startMarker#2), 
              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_Flatten#$T, 
                $LS($LZ), 
                prefix#2, 
                _module.__default.Prepend(_module._default.Lemma_Flatten#$T, $LS($LZ), startMarker#2, M#2))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(267,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Lemma__FlattenAppend0(_module._default.Lemma_FlattenAppend0$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.Lemma_FlattenAppend0$T)
         && $IsAllocBox(startMarker#0, _module._default.Lemma_FlattenAppend0$T, $Heap));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Lemma__FlattenAppend0(_module._default.Lemma_FlattenAppend0$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0), 
    startMarker#0: Box
       where $IsBox(startMarker#0, _module._default.Lemma_FlattenAppend0$T)
         && $IsAllocBox(startMarker#0, _module._default.Lemma_FlattenAppend0$T, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0$T, $LS($LZ), s#0, M#0, startMarker#0))
     && $IsA#_module.Stream(_module.__default.append(_module._default.Lemma_FlattenAppend0$T, 
        $LS($LZ), 
        s#0, 
        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#0, 
          startMarker#0)))
     && 
    _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_FlattenAppend0$T, s#0, M#0, startMarker#0)
     && 
    _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_FlattenAppend0$T, 
      Lit(#_module.Stream.Nil()), 
      M#0, 
      startMarker#0)
     && _module.__default.append#canCall(_module._default.Lemma_FlattenAppend0$T, 
      s#0, 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#0, 
        startMarker#0));
  ensures $Eq#_module.Stream(_module._default.Lemma_FlattenAppend0$T, 
    _module._default.Lemma_FlattenAppend0$T, 
    $LS($LS($LZ)), 
    _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0$T, $LS($LS($LZ)), s#0, M#0, startMarker#0), 
    _module.__default.append(_module._default.Lemma_FlattenAppend0$T, 
      $LS($LS($LZ)), 
      s#0, 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0$T, 
        $LS($LS($LZ)), 
        Lit(#_module.Stream.Nil()), 
        M#0, 
        startMarker#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, M#1} CoCall$$_module.__default.Lemma__FlattenAppend0_h(_module._default.Lemma_FlattenAppend0#$T: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T), $Heap)
         && $IsA#_module.Stream(s#1), 
    M#1: DatatypeType
       where $Is(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T)))
         && $IsAlloc(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T)), 
          $Heap)
         && $IsA#_module.Stream(M#1), 
    startMarker#1: Box
       where $IsBox(startMarker#1, _module._default.Lemma_FlattenAppend0#$T)
         && $IsAllocBox(startMarker#1, _module._default.Lemma_FlattenAppend0#$T, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_FlattenAppend0#$T, s#1, M#1, startMarker#1)
     && 
    _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_FlattenAppend0#$T, 
      Lit(#_module.Stream.Nil()), 
      M#1, 
      startMarker#1)
     && _module.__default.append#canCall(_module._default.Lemma_FlattenAppend0#$T, 
      s#1, 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#1, 
        startMarker#1));
  free ensures $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
    _module._default.Lemma_FlattenAppend0#$T, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LZ), s#1, M#1, startMarker#1), 
    _module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
      $LS($LZ), 
      s#1, 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#1, 
        startMarker#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, M#1} Impl$$_module.__default.Lemma__FlattenAppend0_h(_module._default.Lemma_FlattenAppend0#$T: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T), $Heap)
         && $IsA#_module.Stream(s#1), 
    M#1: DatatypeType
       where $Is(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T)))
         && $IsAlloc(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T)), 
          $Heap)
         && $IsA#_module.Stream(M#1), 
    startMarker#1: Box
       where $IsBox(startMarker#1, _module._default.Lemma_FlattenAppend0#$T)
         && $IsAllocBox(startMarker#1, _module._default.Lemma_FlattenAppend0#$T, $Heap))
   returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_FlattenAppend0#$T, s#1, M#1, startMarker#1)
     && 
    _module.__default.PrependThenFlattenStartMarker#canCall(_module._default.Lemma_FlattenAppend0#$T, 
      Lit(#_module.Stream.Nil()), 
      M#1, 
      startMarker#1)
     && _module.__default.append#canCall(_module._default.Lemma_FlattenAppend0#$T, 
      s#1, 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#1, 
        startMarker#1));
  ensures $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
      _module._default.Lemma_FlattenAppend0#$T, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LZ), s#1, M#1, startMarker#1), 
      _module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
        $LS($LZ), 
        s#1, 
        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#1, 
          startMarker#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LS($LZ)), s#1, M#1, startMarker#1))
       ==> _module.Stream.Nil_q(_module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
          $LS($LS($LZ)), 
          s#1, 
          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
            $LS($LS($LZ)), 
            Lit(#_module.Stream.Nil()), 
            M#1, 
            startMarker#1))));
  ensures $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
      _module._default.Lemma_FlattenAppend0#$T, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LZ), s#1, M#1, startMarker#1), 
      _module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
        $LS($LZ), 
        s#1, 
        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#1, 
          startMarker#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LS($LZ)), s#1, M#1, startMarker#1))
       ==> _module.Stream.Cons_q(_module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
            $LS($LS($LZ)), 
            s#1, 
            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
              $LS($LS($LZ)), 
              Lit(#_module.Stream.Nil()), 
              M#1, 
              startMarker#1)))
         && 
        _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LS($LZ)), s#1, M#1, startMarker#1))
           == _module.Stream.head(_module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
              $LS($LS($LZ)), 
              s#1, 
              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
                $LS($LS($LZ)), 
                Lit(#_module.Stream.Nil()), 
                M#1, 
                startMarker#1)))
         && $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
          _module._default.Lemma_FlattenAppend0#$T, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LS($LZ)), s#1, M#1, startMarker#1)), 
          _module.Stream.tail(_module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
              $LS($LS($LZ)), 
              s#1, 
              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
                $LS($LS($LZ)), 
                Lit(#_module.Stream.Nil()), 
                M#1, 
                startMarker#1)))));
  ensures $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
      _module._default.Lemma_FlattenAppend0#$T, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LZ), s#1, M#1, startMarker#1), 
      _module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
        $LS($LZ), 
        s#1, 
        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#1, 
          startMarker#1)))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LS($LZ)), s#1, M#1, startMarker#1))
           ==> _module.Stream.Nil_q(_module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
              $LS($LS($LZ)), 
              s#1, 
              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
                $LS($LS($LZ)), 
                Lit(#_module.Stream.Nil()), 
                M#1, 
                startMarker#1))))
         && (_module.Stream.Cons_q(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LS($LZ)), s#1, M#1, startMarker#1))
           ==> _module.Stream.Cons_q(_module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
                $LS($LS($LZ)), 
                s#1, 
                _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
                  $LS($LS($LZ)), 
                  Lit(#_module.Stream.Nil()), 
                  M#1, 
                  startMarker#1)))
             && 
            _module.Stream.head(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LS($LZ)), s#1, M#1, startMarker#1))
               == _module.Stream.head(_module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
                  $LS($LS($LZ)), 
                  s#1, 
                  _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
                    $LS($LS($LZ)), 
                    Lit(#_module.Stream.Nil()), 
                    M#1, 
                    startMarker#1)))
             && $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
              _module._default.Lemma_FlattenAppend0#$T, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LS($LZ)), s#1, M#1, startMarker#1)), 
              _module.Stream.tail(_module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
                  $LS($LS($LZ)), 
                  s#1, 
                  _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
                    $LS($LS($LZ)), 
                    Lit(#_module.Stream.Nil()), 
                    M#1, 
                    startMarker#1))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
        _module._default.Lemma_FlattenAppend0#$T, 
        $LS($LS($LZ)), 
        _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LZ), s#1, M#1, startMarker#1), 
        _module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
          $LS($LZ), 
          s#1, 
          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
            $LS($LZ), 
            Lit(#_module.Stream.Nil()), 
            M#1, 
            startMarker#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, M#1} Impl$$_module.__default.Lemma__FlattenAppend0_h(_module._default.Lemma_FlattenAppend0#$T: Ty, 
    _k#0: Box, 
    s#1: DatatypeType, 
    M#1: DatatypeType, 
    startMarker#1: Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tl#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var hd#0: Box;
  var let#0_0_1#0#0: Box;
  var _k##0: Box;
  var s##0: DatatypeType;
  var M##0: DatatypeType;
  var startMarker##0: Box;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Lemma_FlattenAppend0#, Impl$$_module.__default.Lemma__FlattenAppend0_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(331,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Stream(M#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType, $ih#M0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T))
           && $Is($ih#M0#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T)))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
          _module._default.Lemma_FlattenAppend0#$T, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
            $LS($LZ), 
            $ih#s0#0, 
            $ih#M0#0, 
            startMarker#1), 
          _module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
            $LS($LZ), 
            $ih#s0#0, 
            _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
              $LS($LZ), 
              Lit(#_module.Stream.Nil()), 
              $ih#M0#0, 
              startMarker#1))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(333,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (s#1 == #_module.Stream.Nil())
        {
        }
        else if (s#1 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.Lemma_FlattenAppend0#$T)
               && $IsAllocBox(_mcc#0#0, _module._default.Lemma_FlattenAppend0#$T, $Heap);
            assume $Is(_mcc#1#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T), $Heap);
            havoc tl#0;
            assume $Is(tl#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T))
               && $IsAlloc(tl#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T));
            assume tl#0 == let#0_0_0#0#0;
            havoc hd#0;
            assume $IsBox(hd#0, _module._default.Lemma_FlattenAppend0#$T)
               && $IsAllocBox(hd#0, _module._default.Lemma_FlattenAppend0#$T, $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0_0_1#0#0, _module._default.Lemma_FlattenAppend0#$T);
            assume hd#0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(337,27)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##0 := tl#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := M#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            startMarker##0 := startMarker#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Lemma__FlattenAppend0_h(_module._default.Lemma_FlattenAppend0#$T, _k##0, s##0, M##0, startMarker##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(337,46)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(331,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, s#2: DatatypeType, M#2: DatatypeType, startMarker#2: Box :: 
          $Is(s#2, Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T))
               && $Is(M#2, 
                Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend0#$T)))
               && $IsBox(startMarker#2, _module._default.Lemma_FlattenAppend0#$T)
               && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend0#$T, 
              _module._default.Lemma_FlattenAppend0#$T, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, $LS($LZ), s#2, M#2, startMarker#2), 
              _module.__default.append(_module._default.Lemma_FlattenAppend0#$T, 
                $LS($LZ), 
                s#2, 
                _module.__default.PrependThenFlattenStartMarker(_module._default.Lemma_FlattenAppend0#$T, 
                  $LS($LZ), 
                  Lit(#_module.Stream.Nil()), 
                  M#2, 
                  startMarker#2))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(331,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Lemma__FlattenAppend1(_module._default.Lemma_FlattenAppend1$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Lemma__FlattenAppend1(_module._default.Lemma_FlattenAppend1$T: Ty, 
    s#0: DatatypeType, 
    M#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##M#0: DatatypeType;
  var ##prefix#0: DatatypeType;
  var ##M#1: DatatypeType;
  var ##prefix#1: DatatypeType;
  var ##M#2: DatatypeType;
  var ##M#3: DatatypeType;
  var ##N#0: DatatypeType;

    // AddMethodImpl: Lemma_FlattenAppend1, CheckWellformed$$_module.__default.Lemma__FlattenAppend1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(341,15): initial state"} true;
    ##M#0 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#0, 
      Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T)), 
      $Heap);
    assume _module.__default.StreamOfNonEmpties#canCall(_module._default.Lemma_FlattenAppend1$T, M#0);
    assume _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LZ), M#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(343,45): post-state"} true;
    ##prefix#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##prefix#0, 
      Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T), 
      $Heap);
    ##M#1 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#1, 
      Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T)), 
      $Heap);
    assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LS($LZ)), ##M#1);
    assume _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LZ), ##M#1);
    assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_FlattenAppend1$T, s#0, M#0);
    ##prefix#1 := Lit(#_module.Stream.Nil());
    // assume allocatedness for argument to function
    assume $IsAlloc(##prefix#1, 
      Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T), 
      $Heap);
    ##M#2 := M#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#2, 
      Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T)), 
      $Heap);
    assert {:subsumption 0} _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LS($LZ)), ##M#2);
    assume _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LZ), ##M#2);
    assume _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_FlattenAppend1$T, Lit(#_module.Stream.Nil()), M#0);
    ##M#3 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##M#3, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T), $Heap);
    ##N#0 := _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, 
      $LS($LZ), 
      Lit(#_module.Stream.Nil()), 
      M#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##N#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T), $Heap);
    assume _module.__default.append#canCall(_module._default.Lemma_FlattenAppend1$T, 
      s#0, 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#0));
    assume $Eq#_module.Stream(_module._default.Lemma_FlattenAppend1$T, 
      _module._default.Lemma_FlattenAppend1$T, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LZ), s#0, M#0), 
      _module.__default.append(_module._default.Lemma_FlattenAppend1$T, 
        $LS($LZ), 
        s#0, 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#0)));
}



procedure Call$$_module.__default.Lemma__FlattenAppend1(_module._default.Lemma_FlattenAppend1$T: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T), $Heap)
         && $IsA#_module.Stream(s#0), 
    M#0: DatatypeType
       where $Is(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T)))
         && $IsAlloc(M#0, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1$T)), 
          $Heap)
         && $IsA#_module.Stream(M#0));
  // user-defined preconditions
  requires _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LS($LZ)), M#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LZ), s#0, M#0))
     && $IsA#_module.Stream(_module.__default.append(_module._default.Lemma_FlattenAppend1$T, 
        $LS($LZ), 
        s#0, 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#0)))
     && 
    _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_FlattenAppend1$T, s#0, M#0)
     && 
    _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_FlattenAppend1$T, Lit(#_module.Stream.Nil()), M#0)
     && _module.__default.append#canCall(_module._default.Lemma_FlattenAppend1$T, 
      s#0, 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#0));
  ensures $Eq#_module.Stream(_module._default.Lemma_FlattenAppend1$T, 
    _module._default.Lemma_FlattenAppend1$T, 
    $LS($LS($LZ)), 
    _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, $LS($LS($LZ)), s#0, M#0), 
    _module.__default.append(_module._default.Lemma_FlattenAppend1$T, 
      $LS($LS($LZ)), 
      s#0, 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1$T, 
        $LS($LS($LZ)), 
        Lit(#_module.Stream.Nil()), 
        M#0)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, M#1} CoCall$$_module.__default.Lemma__FlattenAppend1_h(_module._default.Lemma_FlattenAppend1#$T: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T), $Heap)
         && $IsA#_module.Stream(s#1), 
    M#1: DatatypeType
       where $Is(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T)))
         && $IsAlloc(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T)), 
          $Heap)
         && $IsA#_module.Stream(M#1));
  // user-defined preconditions
  requires _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), M#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_FlattenAppend1#$T, s#1, M#1)
     && 
    _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_FlattenAppend1#$T, Lit(#_module.Stream.Nil()), M#1)
     && _module.__default.append#canCall(_module._default.Lemma_FlattenAppend1#$T, 
      s#1, 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#1));
  free ensures $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
    _module._default.Lemma_FlattenAppend1#$T, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), s#1, M#1), 
    _module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
      $LS($LZ), 
      s#1, 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, M#1} Impl$$_module.__default.Lemma__FlattenAppend1_h(_module._default.Lemma_FlattenAppend1#$T: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T), $Heap)
         && $IsA#_module.Stream(s#1), 
    M#1: DatatypeType
       where $Is(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T)))
         && $IsAlloc(M#1, 
          Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T)), 
          $Heap)
         && $IsA#_module.Stream(M#1))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), M#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_FlattenAppend1#$T, s#1, M#1)
     && 
    _module.__default.PrependThenFlattenNonEmpties#canCall(_module._default.Lemma_FlattenAppend1#$T, Lit(#_module.Stream.Nil()), M#1)
     && _module.__default.append#canCall(_module._default.Lemma_FlattenAppend1#$T, 
      s#1, 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
        $LS($LZ), 
        Lit(#_module.Stream.Nil()), 
        M#1));
  ensures $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
      _module._default.Lemma_FlattenAppend1#$T, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), s#1, M#1), 
      _module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
        $LS($LZ), 
        s#1, 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), s#1, M#1))
       ==> _module.Stream.Nil_q(_module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
          $LS($LS($LZ)), 
          s#1, 
          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
            $LS($LS($LZ)), 
            Lit(#_module.Stream.Nil()), 
            M#1))));
  ensures $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
      _module._default.Lemma_FlattenAppend1#$T, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), s#1, M#1), 
      _module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
        $LS($LZ), 
        s#1, 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#1)))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), s#1, M#1))
       ==> _module.Stream.Cons_q(_module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
            $LS($LS($LZ)), 
            s#1, 
            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
              $LS($LS($LZ)), 
              Lit(#_module.Stream.Nil()), 
              M#1)))
         && 
        _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), s#1, M#1))
           == _module.Stream.head(_module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
              $LS($LS($LZ)), 
              s#1, 
              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
                $LS($LS($LZ)), 
                Lit(#_module.Stream.Nil()), 
                M#1)))
         && $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
          _module._default.Lemma_FlattenAppend1#$T, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), s#1, M#1)), 
          _module.Stream.tail(_module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
              $LS($LS($LZ)), 
              s#1, 
              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
                $LS($LS($LZ)), 
                Lit(#_module.Stream.Nil()), 
                M#1)))));
  ensures $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
      _module._default.Lemma_FlattenAppend1#$T, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), s#1, M#1), 
      _module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
        $LS($LZ), 
        s#1, 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
          $LS($LZ), 
          Lit(#_module.Stream.Nil()), 
          M#1)))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.Stream.Nil_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), s#1, M#1))
           ==> _module.Stream.Nil_q(_module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
              $LS($LS($LZ)), 
              s#1, 
              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
                $LS($LS($LZ)), 
                Lit(#_module.Stream.Nil()), 
                M#1))))
         && (_module.Stream.Cons_q(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), s#1, M#1))
           ==> _module.Stream.Cons_q(_module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
                $LS($LS($LZ)), 
                s#1, 
                _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
                  $LS($LS($LZ)), 
                  Lit(#_module.Stream.Nil()), 
                  M#1)))
             && 
            _module.Stream.head(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), s#1, M#1))
               == _module.Stream.head(_module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
                  $LS($LS($LZ)), 
                  s#1, 
                  _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
                    $LS($LS($LZ)), 
                    Lit(#_module.Stream.Nil()), 
                    M#1)))
             && $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
              _module._default.Lemma_FlattenAppend1#$T, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LS($LZ)), s#1, M#1)), 
              _module.Stream.tail(_module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
                  $LS($LS($LZ)), 
                  s#1, 
                  _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
                    $LS($LS($LZ)), 
                    Lit(#_module.Stream.Nil()), 
                    M#1))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
        _module._default.Lemma_FlattenAppend1#$T, 
        $LS($LS($LZ)), 
        _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), s#1, M#1), 
        _module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
          $LS($LZ), 
          s#1, 
          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
            $LS($LZ), 
            Lit(#_module.Stream.Nil()), 
            M#1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, M#1} Impl$$_module.__default.Lemma__FlattenAppend1_h(_module._default.Lemma_FlattenAppend1#$T: Ty, 
    _k#0: Box, 
    s#1: DatatypeType, 
    M#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tl#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var hd#0: Box;
  var let#0_0_1#0#0: Box;
  var _k##0: Box;
  var s##0: DatatypeType;
  var M##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Lemma_FlattenAppend1#, Impl$$_module.__default.Lemma__FlattenAppend1_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(341,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Stream(M#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType, $ih#M0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T))
           && $Is($ih#M0#0, 
            Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T)))
           && _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), $ih#M0#0)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
          _module._default.Lemma_FlattenAppend1#$T, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), $ih#s0#0, $ih#M0#0), 
          _module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
            $LS($LZ), 
            $ih#s0#0, 
            _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
              $LS($LZ), 
              Lit(#_module.Stream.Nil()), 
              $ih#M0#0))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(344,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (s#1 == #_module.Stream.Nil())
        {
        }
        else if (s#1 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.Lemma_FlattenAppend1#$T)
               && $IsAllocBox(_mcc#0#0, _module._default.Lemma_FlattenAppend1#$T, $Heap);
            assume $Is(_mcc#1#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T), $Heap);
            havoc tl#0;
            assume $Is(tl#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T))
               && $IsAlloc(tl#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T));
            assume tl#0 == let#0_0_0#0#0;
            havoc hd#0;
            assume $IsBox(hd#0, _module._default.Lemma_FlattenAppend1#$T)
               && $IsAllocBox(hd#0, _module._default.Lemma_FlattenAppend1#$T, $Heap);
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0_0_1#0#0, _module._default.Lemma_FlattenAppend1#$T);
            assume hd#0 == let#0_0_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(348,27)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##0 := tl#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            M##0 := M#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Lemma__FlattenAppend1_h(_module._default.Lemma_FlattenAppend1#$T, _k##0, s##0, M##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(348,33)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(341,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, s#2: DatatypeType, M#2: DatatypeType :: 
          $Is(s#2, Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T))
               && $Is(M#2, 
                Tclass._module.Stream(Tclass._module.Stream(_module._default.Lemma_FlattenAppend1#$T)))
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.StreamOfNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), M#2)
             ==> $PrefixEq#_module.Stream(_module._default.Lemma_FlattenAppend1#$T, 
              _module._default.Lemma_FlattenAppend1#$T, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, $LS($LZ), s#2, M#2), 
              _module.__default.append(_module._default.Lemma_FlattenAppend1#$T, 
                $LS($LZ), 
                s#2, 
                _module.__default.PrependThenFlattenNonEmpties(_module._default.Lemma_FlattenAppend1#$T, 
                  $LS($LZ), 
                  Lit(#_module.Stream.Nil()), 
                  M#2))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Streams.dfy(341,15)"} true;
    }
}



const unique tytagFamily$nat: TyTagFamily;

const unique tytagFamily$object: TyTagFamily;

const unique tytagFamily$array: TyTagFamily;

const unique tytagFamily$_#Func1: TyTagFamily;

const unique tytagFamily$_#PartialFunc1: TyTagFamily;

const unique tytagFamily$_#TotalFunc1: TyTagFamily;

const unique tytagFamily$_#Func0: TyTagFamily;

const unique tytagFamily$_#PartialFunc0: TyTagFamily;

const unique tytagFamily$_#TotalFunc0: TyTagFamily;

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Stream: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
