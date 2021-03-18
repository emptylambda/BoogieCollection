// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy -print:./SimpleCoinduction.bpl

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
function #_module.Stream.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.Stream.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box, a#14#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#14#0#0, a#14#1#0) } 
  DatatypeCtorId(#_module.Stream.Cons(a#14#0#0, a#14#1#0))
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
     ==> (exists a#15#0#0: Box, a#15#1#0: DatatypeType :: 
      d == #_module.Stream.Cons(a#15#0#0, a#15#1#0)));

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
axiom (forall _module.Stream$T: Ty, a#16#0#0: Box, a#16#1#0: DatatypeType :: 
  { $Is(#_module.Stream.Cons(a#16#0#0, a#16#1#0), 
      Tclass._module.Stream(_module.Stream$T)) } 
  $Is(#_module.Stream.Cons(a#16#0#0, a#16#1#0), 
      Tclass._module.Stream(_module.Stream$T))
     <==> $IsBox(a#16#0#0, _module.Stream$T)
       && $Is(a#16#1#0, Tclass._module.Stream(_module.Stream$T)));

// Constructor $IsAlloc
axiom (forall _module.Stream$T: Ty, a#17#0#0: Box, a#17#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Stream.Cons(a#17#0#0, a#17#1#0), 
      Tclass._module.Stream(_module.Stream$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Stream.Cons(a#17#0#0, a#17#1#0), 
        Tclass._module.Stream(_module.Stream$T), 
        $h)
       <==> $IsAllocBox(a#17#0#0, _module.Stream$T, $h)
         && $IsAlloc(a#17#1#0, Tclass._module.Stream(_module.Stream$T), $h)));

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
axiom (forall a#18#0#0: Box, a#18#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#18#0#0, a#18#1#0) } 
  _module.Stream.head(#_module.Stream.Cons(a#18#0#0, a#18#1#0)) == a#18#0#0);

function _module.Stream.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#19#0#0: Box, a#19#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#19#0#0, a#19#1#0) } 
  _module.Stream.tail(#_module.Stream.Cons(a#19#0#0, a#19#1#0)) == a#19#1#0);

// Depth-one case-split function
function $IsA#_module.Stream(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Stream(d) } 
  $IsA#_module.Stream(d) ==> _module.Stream.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Stream$T: Ty, d: DatatypeType :: 
  { _module.Stream.Cons_q(d), $Is(d, Tclass._module.Stream(_module.Stream$T)) } 
  $Is(d, Tclass._module.Stream(_module.Stream$T)) ==> _module.Stream.Cons_q(d));

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
       <==> _module.Stream.Cons_q(d0)
         && _module.Stream.Cons_q(d1)
         && (_module.Stream.Cons_q(d0) && _module.Stream.Cons_q(d1)
           ==> _module.Stream.head(d0) == _module.Stream.head(d1)
             && $Eq#_module.Stream(_module.Stream$T#l, 
              _module.Stream$T#r, 
              ly, 
              _module.Stream.tail(d0), 
              _module.Stream.tail(d1)))));

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
           ==> _module.Stream.Cons_q(d0)
             && _module.Stream.Cons_q(d1)
             && (_module.Stream.Cons_q(d0) && _module.Stream.Cons_q(d1)
               ==> _module.Stream.head(d0) == _module.Stream.head(d1)
                 && $PrefixEq#_module.Stream(_module.Stream$T#l, 
                  _module.Stream$T#r, 
                  ORD#Minus(k, ORD#FromNat(1)), 
                  ly, 
                  _module.Stream.tail(d0), 
                  _module.Stream.tail(d1))))
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

// Constructor function declaration
function #_module.IList.Nil() : DatatypeType;

const unique ##_module.IList.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.IList.Nil()) == ##_module.IList.Nil;

function _module.IList.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.IList.Nil_q(d) } 
  _module.IList.Nil_q(d) <==> DatatypeCtorId(d) == ##_module.IList.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.IList.Nil_q(d) } 
  _module.IList.Nil_q(d) ==> d == #_module.IList.Nil());

function Tclass._module.IList(Ty) : Ty;

const unique Tagclass._module.IList: TyTag;

// Tclass._module.IList Tag
axiom (forall _module.IList$T: Ty :: 
  { Tclass._module.IList(_module.IList$T) } 
  Tag(Tclass._module.IList(_module.IList$T)) == Tagclass._module.IList
     && TagFamily(Tclass._module.IList(_module.IList$T)) == tytagFamily$IList);

// Tclass._module.IList injectivity 0
axiom (forall _module.IList$T: Ty :: 
  { Tclass._module.IList(_module.IList$T) } 
  Tclass._module.IList_0(Tclass._module.IList(_module.IList$T)) == _module.IList$T);

function Tclass._module.IList_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.IList
axiom (forall _module.IList$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.IList(_module.IList$T)) } 
  $IsBox(bx, Tclass._module.IList(_module.IList$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.IList(_module.IList$T)));

// Constructor $Is
axiom (forall _module.IList$T: Ty :: 
  { $Is(#_module.IList.Nil(), Tclass._module.IList(_module.IList$T)) } 
  $Is(#_module.IList.Nil(), Tclass._module.IList(_module.IList$T)));

// Constructor $IsAlloc
axiom (forall _module.IList$T: Ty, $h: Heap :: 
  { $IsAlloc(#_module.IList.Nil(), Tclass._module.IList(_module.IList$T), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.IList.Nil(), Tclass._module.IList(_module.IList$T), $h));

// Constructor function declaration
function #_module.IList.ICons(Box, DatatypeType) : DatatypeType;

const unique ##_module.IList.ICons: DtCtorId;

// Constructor identifier
axiom (forall a#24#0#0: Box, a#24#1#0: DatatypeType :: 
  { #_module.IList.ICons(a#24#0#0, a#24#1#0) } 
  DatatypeCtorId(#_module.IList.ICons(a#24#0#0, a#24#1#0))
     == ##_module.IList.ICons);

function _module.IList.ICons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.IList.ICons_q(d) } 
  _module.IList.ICons_q(d) <==> DatatypeCtorId(d) == ##_module.IList.ICons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.IList.ICons_q(d) } 
  _module.IList.ICons_q(d)
     ==> (exists a#25#0#0: Box, a#25#1#0: DatatypeType :: 
      d == #_module.IList.ICons(a#25#0#0, a#25#1#0)));

// Constructor $Is
axiom (forall _module.IList$T: Ty, a#26#0#0: Box, a#26#1#0: DatatypeType :: 
  { $Is(#_module.IList.ICons(a#26#0#0, a#26#1#0), Tclass._module.IList(_module.IList$T)) } 
  $Is(#_module.IList.ICons(a#26#0#0, a#26#1#0), Tclass._module.IList(_module.IList$T))
     <==> $IsBox(a#26#0#0, _module.IList$T)
       && $Is(a#26#1#0, Tclass._module.IList(_module.IList$T)));

// Constructor $IsAlloc
axiom (forall _module.IList$T: Ty, a#27#0#0: Box, a#27#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.IList.ICons(a#27#0#0, a#27#1#0), 
      Tclass._module.IList(_module.IList$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.IList.ICons(a#27#0#0, a#27#1#0), 
        Tclass._module.IList(_module.IList$T), 
        $h)
       <==> $IsAllocBox(a#27#0#0, _module.IList$T, $h)
         && $IsAlloc(a#27#1#0, Tclass._module.IList(_module.IList$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.IList$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.IList.head(d), _module.IList$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.IList.ICons_q(d)
       && $IsAlloc(d, Tclass._module.IList(_module.IList$T), $h)
     ==> $IsAllocBox(_module.IList.head(d), _module.IList$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.IList$T: Ty, $h: Heap :: 
  { $IsAlloc(_module.IList.tail(d), Tclass._module.IList(_module.IList$T), $h) } 
  $IsGoodHeap($h)
       && 
      _module.IList.ICons_q(d)
       && $IsAlloc(d, Tclass._module.IList(_module.IList$T), $h)
     ==> $IsAlloc(_module.IList.tail(d), Tclass._module.IList(_module.IList$T), $h));

function _module.IList.head(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#28#0#0: Box, a#28#1#0: DatatypeType :: 
  { #_module.IList.ICons(a#28#0#0, a#28#1#0) } 
  _module.IList.head(#_module.IList.ICons(a#28#0#0, a#28#1#0)) == a#28#0#0);

function _module.IList.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#29#0#0: Box, a#29#1#0: DatatypeType :: 
  { #_module.IList.ICons(a#29#0#0, a#29#1#0) } 
  _module.IList.tail(#_module.IList.ICons(a#29#0#0, a#29#1#0)) == a#29#1#0);

// Depth-one case-split function
function $IsA#_module.IList(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.IList(d) } 
  $IsA#_module.IList(d) ==> _module.IList.Nil_q(d) || _module.IList.ICons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.IList$T: Ty, d: DatatypeType :: 
  { _module.IList.ICons_q(d), $Is(d, Tclass._module.IList(_module.IList$T)) } 
    { _module.IList.Nil_q(d), $Is(d, Tclass._module.IList(_module.IList$T)) } 
  $Is(d, Tclass._module.IList(_module.IList$T))
     ==> _module.IList.Nil_q(d) || _module.IList.ICons_q(d));

function $Eq#_module.IList(Ty, Ty, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.IList(_module.IList$T#l))
       && $Is(d1, Tclass._module.IList(_module.IList$T#r))
     ==> ($Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1)
       <==> (_module.IList.Nil_q(d0) && _module.IList.Nil_q(d1))
         || (
          _module.IList.ICons_q(d0)
           && _module.IList.ICons_q(d1)
           && (_module.IList.ICons_q(d0) && _module.IList.ICons_q(d1)
             ==> _module.IList.head(d0) == _module.IList.head(d1)
               && $Eq#_module.IList(_module.IList$T#l, 
                _module.IList$T#r, 
                ly, 
                _module.IList.tail(d0), 
                _module.IList.tail(d1))))));

// Unbump layer co-equality axiom
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1)
     <==> $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, ly, d0, d1));

// Equality for codatatypes
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1)
     <==> d0 == d1);

function $PrefixEq#_module.IList(Ty, Ty, Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.IList(_module.IList$T#l))
       && $Is(d1, Tclass._module.IList(_module.IList$T#r))
     ==> ($PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (_module.IList.Nil_q(d0) && _module.IList.Nil_q(d1))
             || (
              _module.IList.ICons_q(d0)
               && _module.IList.ICons_q(d1)
               && (_module.IList.ICons_q(d0) && _module.IList.ICons_q(d1)
                 ==> _module.IList.head(d0) == _module.IList.head(d1)
                   && $PrefixEq#_module.IList(_module.IList$T#l, 
                    _module.IList$T#r, 
                    ORD#Minus(k, ORD#FromNat(1)), 
                    ly, 
                    _module.IList.tail(d0), 
                    _module.IList.tail(d1)))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k)
           ==> $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k
         ==> $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.IList(_module.IList$T#l, _module.IList$T#r, $LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType, 
    m: Box :: 
  { $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1), $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, m, $LS(ly), d0, d1) } 
  ORD#Less(k, m)
       && $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall _module.IList$T#l: Ty, 
    _module.IList$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1) } 
  d0 == d1
     ==> $PrefixEq#_module.IList(_module.IList$T#l, _module.IList$T#r, k, $LS(ly), d0, d1));

const unique class._module.IList: ClassName;

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

// function declaration for _module._default.Pos
function _module.__default.Pos($ly: LayerType, s#0: DatatypeType) : bool;

function _module.__default.Pos#canCall(s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.Pos($LS($ly), s#0) } 
  _module.__default.Pos($LS($ly), s#0) == _module.__default.Pos($ly, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.Pos(AsFuelBottom($ly), s#0) } 
  _module.__default.Pos($ly, s#0) == _module.__default.Pos($LZ, s#0));

// consequence axiom for _module.__default.Pos
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.Pos($ly, s#0) } 
    _module.__default.Pos#canCall(s#0)
         || (1 != $FunctionContextHeight && $Is(s#0, Tclass._module.Stream(TInt)))
       ==> true);

function _module.__default.Pos#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.Pos
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.Pos#requires($ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(TInt))
     ==> _module.__default.Pos#requires($ly, s#0) == true);

// definition axiom for _module.__default.Pos (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.Pos($LS($ly), s#0) } 
    _module.__default.Pos#canCall(s#0)
         || (1 != $FunctionContextHeight && $Is(s#0, Tclass._module.Stream(TInt)))
       ==> _module.Stream.Cons_q(s#0)
         && ($Unbox(_module.Stream.head(s#0)): int > 0
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.Pos#canCall(_module.Stream.tail(s#0)))
         && _module.__default.Pos($LS($ly), s#0)
           == ($Unbox(_module.Stream.head(s#0)): int > 0
             && _module.__default.Pos($ly, _module.Stream.tail(s#0))));

// 1st prefix predicate axiom for _module.__default.Pos_h
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.Pos($LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(TInt)) && _module.__default.Pos($LS($ly), s#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.Pos_h($LS($ly), _k#0, s#0) } 
        _module.__default.Pos_h($LS($ly), _k#0, s#0)));

// 2nd prefix predicate axiom
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.Pos($LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(TInt))
         && (forall _k#0: Box :: 
          { _module.__default.Pos_h($LS($ly), _k#0, s#0) } 
          _module.__default.Pos_h($LS($ly), _k#0, s#0))
       ==> _module.__default.Pos($LS($ly), s#0));

// 3rd prefix predicate axiom
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, _k#0: Box :: 
    { _module.__default.Pos_h($ly, _k#0, s#0) } 
    $Is(s#0, Tclass._module.Stream(TInt)) && _k#0 == ORD#FromNat(0)
       ==> _module.__default.Pos_h($ly, _k#0, s#0));

procedure CheckWellformed$$_module.__default.Pos(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(TInt)));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Pos(s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Pos
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(9,19): initial state"} true;
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
        assume _module.Stream.Cons_q(s#0);
        if ($Unbox(_module.Stream.head(s#0)): int > 0)
        {
            assume _module.Stream.Cons_q(s#0);
            ##s#0 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Pos#canCall(_module.Stream.tail(s#0));
        }

        assume _module.__default.Pos($LS($LZ), s#0)
           == ($Unbox(_module.Stream.head(s#0)): int > 0
             && _module.__default.Pos($LS($LZ), _module.Stream.tail(s#0)));
        assume _module.Stream.Cons_q(s#0)
           && ($Unbox(_module.Stream.head(s#0)): int > 0
             ==> _module.Stream.Cons_q(s#0)
               && _module.__default.Pos#canCall(_module.Stream.tail(s#0)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Pos($LS($LZ), s#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Pos#
function _module.__default.Pos_h($ly: LayerType, _k#0: Box, s#0: DatatypeType) : bool;

function _module.__default.Pos_h#canCall(_k#0: Box, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.Pos_h($LS($ly), _k#0, s#0) } 
  _module.__default.Pos_h($LS($ly), _k#0, s#0)
     == _module.__default.Pos_h($ly, _k#0, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.Pos_h(AsFuelBottom($ly), _k#0, s#0) } 
  _module.__default.Pos_h($ly, _k#0, s#0)
     == _module.__default.Pos_h($LZ, _k#0, s#0));

// consequence axiom for _module.__default.Pos_h
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.Pos_h($ly, _k#0, s#0) } 
    _module.__default.Pos_h#canCall(_k#0, s#0)
         || (2 != $FunctionContextHeight && $Is(s#0, Tclass._module.Stream(TInt)))
       ==> true);

function _module.__default.Pos_h#requires(LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.Pos_h
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.Pos_h#requires($ly, _k#0, s#0) } 
  $Is(s#0, Tclass._module.Stream(TInt))
     ==> _module.__default.Pos_h#requires($ly, _k#0, s#0) == true);

// definition axiom for _module.__default.Pos_h (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.Pos_h($LS($ly), _k#0, s#0) } 
    _module.__default.Pos_h#canCall(_k#0, s#0)
         || (2 != $FunctionContextHeight && $Is(s#0, Tclass._module.Stream(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && ($Unbox(_module.Stream.head(s#0)): int > 0
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.Pos_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(_module.Stream.head(s#0)): int > 0
             && _module.__default.Pos_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.Pos_h($ly, _k'#0, s#0) } 
            ORD#Less(_k'#0, _k#0) ==> _module.__default.Pos_h#canCall(_k'#0, s#0)))
         && _module.__default.Pos_h($LS($ly), _k#0, s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(_module.Stream.head(s#0)): int > 0
                 && _module.__default.Pos_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.Pos_h($ly, _k'#0, s#0) } 
                ORD#Less(_k'#0, _k#0) ==> _module.__default.Pos_h($ly, _k'#0, s#0)))));

// definition axiom for _module.__default.Pos_h for decreasing-related literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.Pos_h($LS($ly), Lit(_k#0), s#0) } 
    _module.__default.Pos_h#canCall(Lit(_k#0), s#0)
         || (2 != $FunctionContextHeight && $Is(s#0, Tclass._module.Stream(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && ($Unbox(_module.Stream.head(s#0)): int > 0
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.Pos_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(_module.Stream.head(s#0)): int > 0
             && _module.__default.Pos_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.Pos_h($LS($ly), _k'#1, s#0) } 
            ORD#Less(_k'#1, _k#0) ==> _module.__default.Pos_h#canCall(_k'#1, s#0)))
         && _module.__default.Pos_h($LS($ly), Lit(_k#0), s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(_module.Stream.head(s#0)): int > 0
                 && _module.__default.Pos_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.Pos_h($LS($ly), _k'#1, s#0) } 
                ORD#Less(_k'#1, _k#0) ==> _module.__default.Pos_h($LS($ly), _k'#1, s#0)))));

// definition axiom for _module.__default.Pos_h for all literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.Pos_h($LS($ly), Lit(_k#0), Lit(s#0)) } 
    _module.__default.Pos_h#canCall(Lit(_k#0), Lit(s#0))
         || (2 != $FunctionContextHeight && $Is(s#0, Tclass._module.Stream(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && ($Unbox(_module.Stream.head(s#0)): int > 0
               ==> _module.Stream.Cons_q(s#0)
                 && _module.__default.Pos_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> $Unbox(_module.Stream.head(s#0)): int > 0
             && _module.__default.Pos_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.Pos_h($LS($ly), _k'#2, s#0) } 
            ORD#Less(_k'#2, _k#0) ==> _module.__default.Pos_h#canCall(_k'#2, s#0)))
         && _module.__default.Pos_h($LS($ly), Lit(_k#0), Lit(s#0))
           == ((0 < ORD#Offset(_k#0)
               ==> $Unbox(_module.Stream.head(s#0)): int > 0
                 && _module.__default.Pos_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.Pos_h($LS($ly), _k'#2, s#0) } 
                ORD#Less(_k'#2, _k#0) ==> _module.__default.Pos_h($LS($ly), _k'#2, s#0)))));

// function declaration for _module._default.Up
function _module.__default.Up($ly: LayerType, n#0: int) : DatatypeType;

function _module.__default.Up#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Up($LS($ly), n#0) } 
  _module.__default.Up($LS($ly), n#0) == _module.__default.Up($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Up(AsFuelBottom($ly), n#0) } 
  _module.__default.Up($ly, n#0) == _module.__default.Up($LZ, n#0));

// consequence axiom for _module.__default.Up
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Up($ly, n#0) } 
    _module.__default.Up#canCall(n#0) || 4 != $FunctionContextHeight
       ==> $Is(_module.__default.Up($ly, n#0), Tclass._module.Stream(TInt)));

function _module.__default.Up#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.Up
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Up#requires($ly, n#0) } 
  _module.__default.Up#requires($ly, n#0) == true);

// definition axiom for _module.__default.Up (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Up($LS($ly), n#0) } 
    _module.__default.Up#canCall(n#0) || 4 != $FunctionContextHeight
       ==> _module.__default.Up#canCall(n#0 + 1)
         && _module.__default.Up($LS($ly), n#0)
           == #_module.Stream.Cons($Box(n#0), _module.__default.Up($ly, n#0 + 1)));

procedure CheckWellformed$$_module.__default.Up(n#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Up(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Up
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(14,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Up($LS($LZ), n#0), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##n#0 := n#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, TInt, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Up#canCall(n#0 + 1);
        assume _module.Stream.Cons_q(_module.__default.Up($LS($LZ), n#0 + 1));
        assume _module.__default.Up($LS($LZ), n#0)
           == #_module.Stream.Cons($Box(n#0), _module.__default.Up($LS($LZ), n#0 + 1));
        assume _module.__default.Up#canCall(n#0 + 1);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Up($LS($LZ), n#0), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Inc
function _module.__default.Inc($ly: LayerType, s#0: DatatypeType) : DatatypeType;

function _module.__default.Inc#canCall(s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.Inc($LS($ly), s#0) } 
  _module.__default.Inc($LS($ly), s#0) == _module.__default.Inc($ly, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.Inc(AsFuelBottom($ly), s#0) } 
  _module.__default.Inc($ly, s#0) == _module.__default.Inc($LZ, s#0));

// consequence axiom for _module.__default.Inc
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.Inc($ly, s#0) } 
    _module.__default.Inc#canCall(s#0)
         || (3 != $FunctionContextHeight && $Is(s#0, Tclass._module.Stream(TInt)))
       ==> $Is(_module.__default.Inc($ly, s#0), Tclass._module.Stream(TInt)));

function _module.__default.Inc#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.Inc
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.Inc#requires($ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(TInt))
     ==> _module.__default.Inc#requires($ly, s#0) == true);

// definition axiom for _module.__default.Inc (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.Inc($LS($ly), s#0) } 
    _module.__default.Inc#canCall(s#0)
         || (3 != $FunctionContextHeight && $Is(s#0, Tclass._module.Stream(TInt)))
       ==> _module.Stream.Cons_q(s#0)
         && 
        _module.Stream.Cons_q(s#0)
         && _module.__default.Inc#canCall(_module.Stream.tail(s#0))
         && _module.__default.Inc($LS($ly), s#0)
           == #_module.Stream.Cons($Box($Unbox(_module.Stream.head(s#0)): int + 1), 
            _module.__default.Inc($ly, _module.Stream.tail(s#0))));

procedure CheckWellformed$$_module.__default.Inc(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(TInt)));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Inc(s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Inc
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(19,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Inc($LS($LZ), s#0), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(s#0);
        ##s#0 := _module.Stream.tail(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Inc#canCall(_module.Stream.tail(s#0));
        assume _module.Stream.Cons_q(_module.__default.Inc($LS($LZ), _module.Stream.tail(s#0)));
        assume _module.__default.Inc($LS($LZ), s#0)
           == #_module.Stream.Cons($Box($Unbox(_module.Stream.head(s#0)): int + 1), 
            _module.__default.Inc($LS($LZ), _module.Stream.tail(s#0)));
        assume _module.Stream.Cons_q(s#0)
           && 
          _module.Stream.Cons_q(s#0)
           && _module.__default.Inc#canCall(_module.Stream.tail(s#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Inc($LS($LZ), s#0), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



procedure {:induction false} CheckWellformed$$_module.__default.UpLemma(k#0: int where LitInt(0) <= k#0, n#0: int);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:induction false} CheckWellformed$$_module.__default.UpLemma(k#0: int, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##s#0: DatatypeType;
  var ##n#1: int;

    // AddMethodImpl: UpLemma, CheckWellformed$$_module.__default.UpLemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(24,25): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(25,21): post-state"} true;
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, TInt, $Heap);
    assume _module.__default.Up#canCall(n#0);
    assume _module.Stream.Cons_q(_module.__default.Up($LS($LZ), n#0));
    ##s#0 := _module.__default.Up($LS($LZ), n#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#0));
    assume _module.Stream.Cons_q(_module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)));
    ##n#1 := n#0 + 1;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, TInt, $Heap);
    assume _module.__default.Up#canCall(n#0 + 1);
    assume _module.Stream.Cons_q(_module.__default.Up($LS($LZ), n#0 + 1));
    assert 0 <= k#0;
    assume $PrefixEq#_module.Stream(TInt, 
      TInt, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)), 
      _module.__default.Up($LS($LZ), n#0 + 1));
}



procedure {:induction false} Call$$_module.__default.UpLemma(k#0: int where LitInt(0) <= k#0, n#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Up#canCall(n#0)
     && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#0))
     && _module.__default.Up#canCall(n#0 + 1);
  free ensures $PrefixEq#_module.Stream(TInt, 
    TInt, 
    ORD#FromNat(k#0), 
    $LS($LS($LZ)), 
    _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)), 
    _module.__default.Up($LS($LZ), n#0 + 1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:induction false} Impl$$_module.__default.UpLemma(k#0: int where LitInt(0) <= k#0, n#0: int) returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Up#canCall(n#0)
     && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#0))
     && _module.__default.Up#canCall(n#0 + 1);
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)), 
      _module.__default.Up($LS($LZ), n#0 + 1))
     || (0 < k#0
       ==> 
      _module.Stream.Cons_q(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#0)))
       ==> _module.Stream.Cons_q(_module.__default.Up($LS($LS($LZ)), n#0 + 1))
         && 
        $Unbox(_module.Stream.head(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#0)))): int
           == $Unbox(_module.Stream.head(_module.__default.Up($LS($LS($LZ)), n#0 + 1))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#FromNat(k#0 - 1), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#0))), 
          _module.Stream.tail(_module.__default.Up($LS($LS($LZ)), n#0 + 1))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:induction false} Impl$$_module.__default.UpLemma(k#0: int, n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k##0_0: int;
  var n##0_0: int;

    // AddMethodImpl: UpLemma, Impl$$_module.__default.UpLemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(26,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(27,3)
    assume true;
    if (k#0 != 0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(28,12)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(k#0 - 1, Tclass._System.nat());
        k##0_0 := k#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0_0 := n#0 + 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= k#0 || k##0_0 == k#0;
        assert 0 <= n#0 || k##0_0 < k#0 || n##0_0 == n#0;
        assert k##0_0 < k#0 || (k##0_0 == k#0 && n##0_0 < n#0);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.UpLemma(k##0_0, n##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(28,21)"} true;
    }
    else
    {
    }
}



procedure {:induction false} CheckWellformed$$_module.__default.CoUpLemma(n#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:induction false} Call$$_module.__default.CoUpLemma(n#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)))
     && $IsA#_module.Stream(_module.__default.Up($LS($LZ), n#0 + 1))
     && 
    _module.__default.Up#canCall(n#0)
     && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#0))
     && _module.__default.Up#canCall(n#0 + 1);
  ensures $Eq#_module.Stream(TInt, 
    TInt, 
    $LS($LS($LZ)), 
    _module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#0)), 
    _module.__default.Up($LS($LS($LZ)), n#0 + 1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:induction false} CoCall$$_module.__default.CoUpLemma_h(_k#0: Box, n#1: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Up#canCall(n#1)
     && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#1))
     && _module.__default.Up#canCall(n#1 + 1);
  free ensures $PrefixEq#_module.Stream(TInt, 
    TInt, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#1)), 
    _module.__default.Up($LS($LZ), n#1 + 1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:induction false} Impl$$_module.__default.CoUpLemma_h(_k#0: Box, n#1: int) returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Up#canCall(n#1)
     && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#1))
     && _module.__default.Up#canCall(n#1 + 1);
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#1)), 
      _module.__default.Up($LS($LZ), n#1 + 1))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1)))
       ==> _module.Stream.Cons_q(_module.__default.Up($LS($LS($LZ)), n#1 + 1))
         && 
        $Unbox(_module.Stream.head(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1)))): int
           == $Unbox(_module.Stream.head(_module.__default.Up($LS($LS($LZ)), n#1 + 1))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1))), 
          _module.Stream.tail(_module.__default.Up($LS($LS($LZ)), n#1 + 1))));
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#1)), 
      _module.__default.Up($LS($LZ), n#1 + 1))
     || 
    (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1)))
       ==> _module.Stream.Cons_q(_module.__default.Up($LS($LS($LZ)), n#1 + 1))
         && 
        $Unbox(_module.Stream.head(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1)))): int
           == $Unbox(_module.Stream.head(_module.__default.Up($LS($LS($LZ)), n#1 + 1))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1))), 
          _module.Stream.tail(_module.__default.Up($LS($LS($LZ)), n#1 + 1))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(TInt, 
        TInt, 
        $LS($LS($LZ)), 
        _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#1)), 
        _module.__default.Up($LS($LZ), n#1 + 1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:induction false} Impl$$_module.__default.CoUpLemma_h(_k#0: Box, n#1: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _k##0: Box;
  var n##0: int;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: CoUpLemma#, Impl$$_module.__default.CoUpLemma_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(32,34): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(34,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(35,12)
        // TrCallStmt: Before ProcessCallStmt
        assert ORD#IsNat(Lit(ORD#FromNat(1)));
        assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0 := n#1 + 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call CoCall$$_module.__default.CoUpLemma_h(_k##0, n##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(35,16)"} true;
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(32,35)
        $initHeapForallStmt#0 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#0 == $Heap;
        assume (forall _k'#0: Box, n#2: int :: 
          ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(TInt, 
              TInt, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#2)), 
              _module.__default.Up($LS($LZ), n#2 + 1)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(32,34)"} true;
    }
}



procedure {:_induction k#0, n#0, nn#0} CheckWellformed$$_module.__default.UpLemma__Auto(k#0: int where LitInt(0) <= k#0, n#0: int, nn#0: int);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction k#0, n#0, nn#0} CheckWellformed$$_module.__default.UpLemma__Auto(k#0: int, n#0: int, nn#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##s#0: DatatypeType;
  var ##n#1: int;

    // AddMethodImpl: UpLemma_Auto, CheckWellformed$$_module.__default.UpLemma__Auto
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(38,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(39,20): post-state"} true;
    if (*)
    {
        assume nn#0 == n#0 + 1;
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, TInt, $Heap);
        assume _module.__default.Up#canCall(n#0);
        assume _module.Stream.Cons_q(_module.__default.Up($LS($LZ), n#0));
        ##s#0 := _module.__default.Up($LS($LZ), n#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
        assume _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#0));
        assume _module.Stream.Cons_q(_module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)));
        ##n#1 := nn#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, TInt, $Heap);
        assume _module.__default.Up#canCall(nn#0);
        assume _module.Stream.Cons_q(_module.__default.Up($LS($LZ), nn#0));
        assert 0 <= k#0;
        assume $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#FromNat(k#0), 
          $LS($LS($LZ)), 
          _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)), 
          _module.__default.Up($LS($LZ), nn#0));
    }
    else
    {
        assume nn#0 == n#0 + 1
           ==> $PrefixEq#_module.Stream(TInt, 
            TInt, 
            ORD#FromNat(k#0), 
            $LS($LS($LZ)), 
            _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)), 
            _module.__default.Up($LS($LZ), nn#0));
    }
}



procedure {:_induction k#0, n#0, nn#0} Call$$_module.__default.UpLemma__Auto(k#0: int where LitInt(0) <= k#0, n#0: int, nn#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures nn#0 == n#0 + 1
     ==> _module.__default.Up#canCall(n#0)
       && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#0))
       && _module.__default.Up#canCall(nn#0);
  free ensures nn#0 == n#0 + 1
     ==> $PrefixEq#_module.Stream(TInt, 
      TInt, 
      ORD#FromNat(k#0), 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)), 
      _module.__default.Up($LS($LZ), nn#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, n#0, nn#0} Impl$$_module.__default.UpLemma__Auto(k#0: int where LitInt(0) <= k#0, n#0: int, nn#0: int)
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures nn#0 == n#0 + 1
     ==> _module.__default.Up#canCall(n#0)
       && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#0))
       && _module.__default.Up#canCall(nn#0);
  ensures nn#0 == n#0 + 1
     ==> $PrefixEq#_module.Stream(TInt, 
        TInt, 
        ORD#FromNat(k#0), 
        $LS($LS($LZ)), 
        _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)), 
        _module.__default.Up($LS($LZ), nn#0))
       || (0 < k#0
         ==> 
        _module.Stream.Cons_q(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#0)))
         ==> _module.Stream.Cons_q(_module.__default.Up($LS($LS($LZ)), nn#0))
           && 
          $Unbox(_module.Stream.head(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#0)))): int
             == $Unbox(_module.Stream.head(_module.__default.Up($LS($LS($LZ)), nn#0))): int
           && $PrefixEq#_module.Stream(TInt, 
            TInt, 
            ORD#FromNat(k#0 - 1), 
            $LS($LS($LZ)), 
            _module.Stream.tail(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#0))), 
            _module.Stream.tail(_module.__default.Up($LS($LS($LZ)), nn#0))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, n#0, nn#0} Impl$$_module.__default.UpLemma__Auto(k#0: int, n#0: int, nn#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: UpLemma_Auto, Impl$$_module.__default.UpLemma__Auto
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(40,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, $ih#n0#0: int, $ih#nn0#0: int :: 
      LitInt(0) <= $ih#k0#0
           && Lit(true)
           && ((0 <= $ih#k0#0 && $ih#k0#0 < k#0)
             || ($ih#k0#0 == k#0
               && ((0 <= $ih#n0#0 && $ih#n0#0 < n#0)
                 || ($ih#n0#0 == n#0 && 0 <= $ih#nn0#0 && $ih#nn0#0 < nn#0))))
         ==> 
        $ih#nn0#0 == $ih#n0#0 + 1
         ==> $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#FromNat($ih#k0#0), 
          $LS($LS($LZ)), 
          _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), $ih#n0#0)), 
          _module.__default.Up($LS($LZ), $ih#nn0#0)));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.CoUpLemma__Auto(n#0: int, nn#0: int);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.CoUpLemma__Auto(n#0: int, nn#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures nn#0 == n#0 + 1
     ==> $IsA#_module.Stream(_module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#0)))
       && $IsA#_module.Stream(_module.__default.Up($LS($LZ), nn#0))
       && 
      _module.__default.Up#canCall(n#0)
       && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#0))
       && _module.__default.Up#canCall(nn#0);
  ensures nn#0 == n#0 + 1
     ==> $Eq#_module.Stream(TInt, 
      TInt, 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#0)), 
      _module.__default.Up($LS($LS($LZ)), nn#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, n#1, nn#1} CoCall$$_module.__default.CoUpLemma__Auto_h(_k#0: Box, n#1: int, nn#1: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures nn#1 == n#1 + 1
     ==> _module.__default.Up#canCall(n#1)
       && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#1))
       && _module.__default.Up#canCall(nn#1);
  free ensures nn#1 == n#1 + 1
     ==> $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#1)), 
      _module.__default.Up($LS($LZ), nn#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, n#1, nn#1} Impl$$_module.__default.CoUpLemma__Auto_h(_k#0: Box, n#1: int, nn#1: int) returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures nn#1 == n#1 + 1
     ==> _module.__default.Up#canCall(n#1)
       && _module.__default.Inc#canCall(_module.__default.Up($LS($LZ), n#1))
       && _module.__default.Up#canCall(nn#1);
  ensures nn#1 == n#1 + 1
     ==> $PrefixEq#_module.Stream(TInt, 
        TInt, 
        _k#0, 
        $LS($LS($LZ)), 
        _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#1)), 
        _module.__default.Up($LS($LZ), nn#1))
       || (0 < ORD#Offset(_k#0)
         ==> 
        _module.Stream.Cons_q(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1)))
         ==> _module.Stream.Cons_q(_module.__default.Up($LS($LS($LZ)), nn#1))
           && 
          $Unbox(_module.Stream.head(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1)))): int
             == $Unbox(_module.Stream.head(_module.__default.Up($LS($LS($LZ)), nn#1))): int
           && $PrefixEq#_module.Stream(TInt, 
            TInt, 
            ORD#Minus(_k#0, ORD#FromNat(1)), 
            $LS($LS($LZ)), 
            _module.Stream.tail(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1))), 
            _module.Stream.tail(_module.__default.Up($LS($LS($LZ)), nn#1))));
  ensures nn#1 == n#1 + 1
     ==> $PrefixEq#_module.Stream(TInt, 
        TInt, 
        _k#0, 
        $LS($LS($LZ)), 
        _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#1)), 
        _module.__default.Up($LS($LZ), nn#1))
       || 
      (0 < ORD#Offset(_k#0)
         ==> 
        _module.Stream.Cons_q(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1)))
         ==> _module.Stream.Cons_q(_module.__default.Up($LS($LS($LZ)), nn#1))
           && 
          $Unbox(_module.Stream.head(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1)))): int
             == $Unbox(_module.Stream.head(_module.__default.Up($LS($LS($LZ)), nn#1))): int
           && $PrefixEq#_module.Stream(TInt, 
            TInt, 
            ORD#Minus(_k#0, ORD#FromNat(1)), 
            $LS($LS($LZ)), 
            _module.Stream.tail(_module.__default.Inc($LS($LS($LZ)), _module.__default.Up($LS($LS($LZ)), n#1))), 
            _module.Stream.tail(_module.__default.Up($LS($LS($LZ)), nn#1))))
       || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
         ==> $Eq#_module.Stream(TInt, 
          TInt, 
          $LS($LS($LZ)), 
          _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#1)), 
          _module.__default.Up($LS($LZ), nn#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, n#1, nn#1} Impl$$_module.__default.CoUpLemma__Auto_h(_k#0: Box, n#1: int, nn#1: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: CoUpLemma_Auto#, Impl$$_module.__default.CoUpLemma__Auto_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(43,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#n0#0: int, $ih#nn0#0: int :: 
      Lit(true)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && ((0 <= $ih#n0#0 && $ih#n0#0 < n#1)
                 || ($ih#n0#0 == n#1 && 0 <= $ih#nn0#0 && $ih#nn0#0 < nn#1))))
         ==> 
        $ih#nn0#0 == $ih#n0#0 + 1
         ==> $PrefixEq#_module.Stream(TInt, 
          TInt, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), $ih#n0#0)), 
          _module.__default.Up($LS($LZ), $ih#nn0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(45,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(43,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, n#2: int, nn#2: int :: 
          ORD#Less(_k'#0, _k#0)
             ==> 
            nn#2 == n#2 + 1
             ==> $PrefixEq#_module.Stream(TInt, 
              TInt, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.Inc($LS($LZ), _module.__default.Up($LS($LZ), n#2)), 
              _module.__default.Up($LS($LZ), nn#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(43,15)"} true;
    }
}



// function declaration for _module._default.Repeat
function _module.__default.Repeat($ly: LayerType, n#0: int) : DatatypeType;

function _module.__default.Repeat#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Repeat($LS($ly), n#0) } 
  _module.__default.Repeat($LS($ly), n#0) == _module.__default.Repeat($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Repeat(AsFuelBottom($ly), n#0) } 
  _module.__default.Repeat($ly, n#0) == _module.__default.Repeat($LZ, n#0));

// consequence axiom for _module.__default.Repeat
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Repeat($ly, n#0) } 
    _module.__default.Repeat#canCall(n#0) || 9 != $FunctionContextHeight
       ==> $Is(_module.__default.Repeat($ly, n#0), Tclass._module.Stream(TInt)));

function _module.__default.Repeat#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.Repeat
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.Repeat#requires($ly, n#0) } 
  _module.__default.Repeat#requires($ly, n#0) == true);

// definition axiom for _module.__default.Repeat (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.Repeat($LS($ly), n#0) } 
    _module.__default.Repeat#canCall(n#0) || 9 != $FunctionContextHeight
       ==> _module.__default.Repeat#canCall(n#0)
         && _module.__default.Repeat($LS($ly), n#0)
           == #_module.Stream.Cons($Box(n#0), _module.__default.Repeat($ly, n#0)));

procedure CheckWellformed$$_module.__default.Repeat(n#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Repeat(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Repeat
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(50,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Repeat($LS($LZ), n#0), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, TInt, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Repeat#canCall(n#0);
        assume _module.Stream.Cons_q(_module.__default.Repeat($LS($LZ), n#0));
        assume _module.__default.Repeat($LS($LZ), n#0)
           == #_module.Stream.Cons($Box(n#0), _module.__default.Repeat($LS($LZ), n#0));
        assume _module.__default.Repeat#canCall(n#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Repeat($LS($LZ), n#0), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.RepeatLemma(n#0: int);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.RepeatLemma(n#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.Inc($LS($LZ), _module.__default.Repeat($LS($LZ), n#0)))
     && $IsA#_module.Stream(_module.__default.Repeat($LS($LZ), n#0 + 1))
     && 
    _module.__default.Repeat#canCall(n#0)
     && _module.__default.Inc#canCall(_module.__default.Repeat($LS($LZ), n#0))
     && _module.__default.Repeat#canCall(n#0 + 1);
  ensures $Eq#_module.Stream(TInt, 
    TInt, 
    $LS($LS($LZ)), 
    _module.__default.Inc($LS($LS($LZ)), _module.__default.Repeat($LS($LS($LZ)), n#0)), 
    _module.__default.Repeat($LS($LS($LZ)), n#0 + 1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, n#1} CoCall$$_module.__default.RepeatLemma_h(_k#0: Box, n#1: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Repeat#canCall(n#1)
     && _module.__default.Inc#canCall(_module.__default.Repeat($LS($LZ), n#1))
     && _module.__default.Repeat#canCall(n#1 + 1);
  free ensures $PrefixEq#_module.Stream(TInt, 
    TInt, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.Inc($LS($LZ), _module.__default.Repeat($LS($LZ), n#1)), 
    _module.__default.Repeat($LS($LZ), n#1 + 1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, n#1} Impl$$_module.__default.RepeatLemma_h(_k#0: Box, n#1: int) returns ($_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Repeat#canCall(n#1)
     && _module.__default.Inc#canCall(_module.__default.Repeat($LS($LZ), n#1))
     && _module.__default.Repeat#canCall(n#1 + 1);
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LZ), _module.__default.Repeat($LS($LZ), n#1)), 
      _module.__default.Repeat($LS($LZ), n#1 + 1))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.Inc($LS($LS($LZ)), _module.__default.Repeat($LS($LS($LZ)), n#1)))
       ==> _module.Stream.Cons_q(_module.__default.Repeat($LS($LS($LZ)), n#1 + 1))
         && 
        $Unbox(_module.Stream.head(_module.__default.Inc($LS($LS($LZ)), _module.__default.Repeat($LS($LS($LZ)), n#1)))): int
           == $Unbox(_module.Stream.head(_module.__default.Repeat($LS($LS($LZ)), n#1 + 1))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Inc($LS($LS($LZ)), _module.__default.Repeat($LS($LS($LZ)), n#1))), 
          _module.Stream.tail(_module.__default.Repeat($LS($LS($LZ)), n#1 + 1))));
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.Inc($LS($LZ), _module.__default.Repeat($LS($LZ), n#1)), 
      _module.__default.Repeat($LS($LZ), n#1 + 1))
     || 
    (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.Inc($LS($LS($LZ)), _module.__default.Repeat($LS($LS($LZ)), n#1)))
       ==> _module.Stream.Cons_q(_module.__default.Repeat($LS($LS($LZ)), n#1 + 1))
         && 
        $Unbox(_module.Stream.head(_module.__default.Inc($LS($LS($LZ)), _module.__default.Repeat($LS($LS($LZ)), n#1)))): int
           == $Unbox(_module.Stream.head(_module.__default.Repeat($LS($LS($LZ)), n#1 + 1))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Inc($LS($LS($LZ)), _module.__default.Repeat($LS($LS($LZ)), n#1))), 
          _module.Stream.tail(_module.__default.Repeat($LS($LS($LZ)), n#1 + 1))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(TInt, 
        TInt, 
        $LS($LS($LZ)), 
        _module.__default.Inc($LS($LZ), _module.__default.Repeat($LS($LZ), n#1)), 
        _module.__default.Repeat($LS($LZ), n#1 + 1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, n#1} Impl$$_module.__default.RepeatLemma_h(_k#0: Box, n#1: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: RepeatLemma#, Impl$$_module.__default.RepeatLemma_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(55,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#n0#0: int :: 
      Lit(true)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && 0 <= $ih#n0#0 && $ih#n0#0 < n#1))
         ==> $PrefixEq#_module.Stream(TInt, 
          TInt, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.Inc($LS($LZ), _module.__default.Repeat($LS($LZ), $ih#n0#0)), 
          _module.__default.Repeat($LS($LZ), $ih#n0#0 + 1)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(57,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(55,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, n#2: int :: 
          ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(TInt, 
              TInt, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.Inc($LS($LZ), _module.__default.Repeat($LS($LZ), n#2)), 
              _module.__default.Repeat($LS($LZ), n#2 + 1)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(55,15)"} true;
    }
}



// function declaration for _module._default.True
function _module.__default.True(_module._default.True$_T0: Ty, $ly: LayerType, s#0: DatatypeType) : bool;

function _module.__default.True#canCall(_module._default.True$_T0: Ty, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.True$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.True(_module._default.True$_T0, $LS($ly), s#0) } 
  _module.__default.True(_module._default.True$_T0, $LS($ly), s#0)
     == _module.__default.True(_module._default.True$_T0, $ly, s#0));

// fuel synonym axiom
axiom (forall _module._default.True$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.True(_module._default.True$_T0, AsFuelBottom($ly), s#0) } 
  _module.__default.True(_module._default.True$_T0, $ly, s#0)
     == _module.__default.True(_module._default.True$_T0, $LZ, s#0));

// consequence axiom for _module.__default.True
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.True$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.True(_module._default.True$_T0, $ly, s#0) } 
    _module.__default.True#canCall(_module._default.True$_T0, s#0)
         || (12 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.True$_T0)))
       ==> true);

function _module.__default.True#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.True
axiom (forall _module._default.True$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.True#requires(_module._default.True$_T0, $ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.True$_T0))
     ==> _module.__default.True#requires(_module._default.True$_T0, $ly, s#0) == true);

// definition axiom for _module.__default.True (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.True$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.True(_module._default.True$_T0, $LS($ly), s#0) } 
    _module.__default.True#canCall(_module._default.True$_T0, s#0)
         || (12 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.True$_T0)))
       ==> _module.Stream.Cons_q(s#0)
         && _module.__default.True#canCall(_module._default.True$_T0, _module.Stream.tail(s#0))
         && _module.__default.True(_module._default.True$_T0, $LS($ly), s#0)
           == _module.__default.True(_module._default.True$_T0, $ly, _module.Stream.tail(s#0)));

// 1st prefix predicate axiom for _module.__default.True_h
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.True#$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.True(_module._default.True#$_T0, $LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.True#$_T0))
         && _module.__default.True(_module._default.True#$_T0, $LS($ly), s#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k#0, s#0) } 
        _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k#0, s#0)));

// 2nd prefix predicate axiom
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.True#$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.True(_module._default.True#$_T0, $LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.True#$_T0))
         && (forall _k#0: Box :: 
          { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k#0, s#0) } 
          _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k#0, s#0))
       ==> _module.__default.True(_module._default.True#$_T0, $LS($ly), s#0));

// 3rd prefix predicate axiom
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.True#$_T0: Ty, $ly: LayerType, s#0: DatatypeType, _k#0: Box :: 
    { _module.__default.True_h(_module._default.True#$_T0, $ly, _k#0, s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.True#$_T0))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.True_h(_module._default.True#$_T0, $ly, _k#0, s#0));

procedure CheckWellformed$$_module.__default.True(_module._default.True$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.True$_T0)));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.True(_module._default.True$_T0: Ty, s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function True
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(62,19): initial state"} true;
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
        assume _module.Stream.Cons_q(s#0);
        ##s#0 := _module.Stream.tail(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.True$_T0), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.True#canCall(_module._default.True$_T0, _module.Stream.tail(s#0));
        assume _module.__default.True(_module._default.True$_T0, $LS($LZ), s#0)
           == _module.__default.True(_module._default.True$_T0, $LS($LZ), _module.Stream.tail(s#0));
        assume _module.Stream.Cons_q(s#0)
           && _module.__default.True#canCall(_module._default.True$_T0, _module.Stream.tail(s#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.True(_module._default.True$_T0, $LS($LZ), s#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.True#
function _module.__default.True_h(_module._default.True#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType)
   : bool;

function _module.__default.True_h#canCall(_module._default.True#$_T0: Ty, _k#0: Box, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.True#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k#0, s#0) } 
  _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k#0, s#0)
     == _module.__default.True_h(_module._default.True#$_T0, $ly, _k#0, s#0));

// fuel synonym axiom
axiom (forall _module._default.True#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.True_h(_module._default.True#$_T0, AsFuelBottom($ly), _k#0, s#0) } 
  _module.__default.True_h(_module._default.True#$_T0, $ly, _k#0, s#0)
     == _module.__default.True_h(_module._default.True#$_T0, $LZ, _k#0, s#0));

// consequence axiom for _module.__default.True_h
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.True#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.True_h(_module._default.True#$_T0, $ly, _k#0, s#0) } 
    _module.__default.True_h#canCall(_module._default.True#$_T0, _k#0, s#0)
         || (13 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.True#$_T0)))
       ==> true);

function _module.__default.True_h#requires(Ty, LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.True_h
axiom (forall _module._default.True#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.True_h#requires(_module._default.True#$_T0, $ly, _k#0, s#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.True#$_T0))
     ==> _module.__default.True_h#requires(_module._default.True#$_T0, $ly, _k#0, s#0)
       == true);

// definition axiom for _module.__default.True_h (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.True#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k#0, s#0) } 
    _module.__default.True_h#canCall(_module._default.True#$_T0, _k#0, s#0)
         || (13 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.True#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.True_h#canCall(_module._default.True#$_T0, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.True_h(_module._default.True#$_T0, 
            $ly, 
            ORD#Minus(_k#0, ORD#FromNat(1)), 
            _module.Stream.tail(s#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.True_h(_module._default.True#$_T0, $ly, _k'#0, s#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.True_h#canCall(_module._default.True#$_T0, _k'#0, s#0)))
         && _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k#0, s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.True_h(_module._default.True#$_T0, 
                $ly, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Stream.tail(s#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.True_h(_module._default.True#$_T0, $ly, _k'#0, s#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.True_h(_module._default.True#$_T0, $ly, _k'#0, s#0)))));

// definition axiom for _module.__default.True_h for decreasing-related literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.True#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), Lit(_k#0), s#0) } 
    _module.__default.True_h#canCall(_module._default.True#$_T0, Lit(_k#0), s#0)
         || (13 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.True#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.True_h#canCall(_module._default.True#$_T0, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.True_h(_module._default.True#$_T0, 
            $LS($ly), 
            ORD#Minus(_k#0, ORD#FromNat(1)), 
            _module.Stream.tail(s#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k'#1, s#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.True_h#canCall(_module._default.True#$_T0, _k'#1, s#0)))
         && _module.__default.True_h(_module._default.True#$_T0, $LS($ly), Lit(_k#0), s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.True_h(_module._default.True#$_T0, 
                $LS($ly), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Stream.tail(s#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k'#1, s#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k'#1, s#0)))));

// definition axiom for _module.__default.True_h for all literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall _module._default.True#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), Lit(_k#0), Lit(s#0)) } 
    _module.__default.True_h#canCall(_module._default.True#$_T0, Lit(_k#0), Lit(s#0))
         || (13 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.True#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.True_h#canCall(_module._default.True#$_T0, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Stream.tail(s#0)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.True_h(_module._default.True#$_T0, 
            $LS($ly), 
            ORD#Minus(_k#0, ORD#FromNat(1)), 
            _module.Stream.tail(s#0)))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k'#2, s#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.True_h#canCall(_module._default.True#$_T0, _k'#2, s#0)))
         && _module.__default.True_h(_module._default.True#$_T0, $LS($ly), Lit(_k#0), Lit(s#0))
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.True_h(_module._default.True#$_T0, 
                $LS($ly), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Stream.tail(s#0)))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k'#2, s#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.True_h(_module._default.True#$_T0, $LS($ly), _k'#2, s#0)))));

procedure CheckWellformed$$_module.__default.AlwaysTrue(_module._default.AlwaysTrue$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.AlwaysTrue$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.AlwaysTrue$_T0), $Heap)
         && $IsA#_module.Stream(s#0));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AlwaysTrue(_module._default.AlwaysTrue$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.AlwaysTrue$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.AlwaysTrue$_T0), $Heap)
         && $IsA#_module.Stream(s#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.True#canCall(_module._default.AlwaysTrue$_T0, s#0);
  free ensures _module.__default.True#canCall(_module._default.AlwaysTrue$_T0, s#0)
     && 
    _module.__default.True(_module._default.AlwaysTrue$_T0, $LS($LZ), s#0)
     && $Is(_module.Stream.tail(s#0), Tclass._module.Stream(_module._default.AlwaysTrue$_T0))
     && _module.__default.True(_module._default.AlwaysTrue$_T0, $LS($LZ), _module.Stream.tail(s#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} CoCall$$_module.__default.AlwaysTrue_h(_module._default.AlwaysTrue#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.AlwaysTrue#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.AlwaysTrue#$_T0), $Heap)
         && $IsA#_module.Stream(s#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.True_h#canCall(_module._default.AlwaysTrue#$_T0, _k#0, s#1);
  free ensures _module.__default.True_h#canCall(_module._default.AlwaysTrue#$_T0, _k#0, s#1)
     && 
    _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LZ), _k#0, s#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> _module.__default.True_h(_module._default.AlwaysTrue#$_T0, 
        $LS($LZ), 
        ORD#Minus(_k#0, ORD#FromNat(1)), 
        _module.Stream.tail(s#1)))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LZ), _k'#0, s#1) } 
        ORD#Less(_k'#0, _k#0)
           ==> _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LZ), _k'#0, s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} Impl$$_module.__default.AlwaysTrue_h(_module._default.AlwaysTrue#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.AlwaysTrue#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.AlwaysTrue#$_T0), $Heap)
         && $IsA#_module.Stream(s#1))
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.True_h#canCall(_module._default.AlwaysTrue#$_T0, _k#0, s#1);
  ensures _module.__default.True_h#canCall(_module._default.AlwaysTrue#$_T0, _k#0, s#1)
     ==> _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LZ), _k#0, s#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.__default.True_h(_module._default.AlwaysTrue#$_T0, 
          $LS($LS($LZ)), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          _module.Stream.tail(s#1)));
  ensures _module.__default.True_h#canCall(_module._default.AlwaysTrue#$_T0, _k#0, s#1)
     ==> _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LZ), _k#0, s#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LS($LZ)), _k'#1, s#1) } 
          ORD#Less(_k'#1, _k#0)
             ==> _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LS($LZ)), _k'#1, s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1} Impl$$_module.__default.AlwaysTrue_h(_module._default.AlwaysTrue#$_T0: Ty, _k#0: Box, s#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: AlwaysTrue#, Impl$$_module.__default.AlwaysTrue_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(67,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.AlwaysTrue#$_T0))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LZ), $ih#_k0#0, $ih#s0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(69,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(67,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, s#2: DatatypeType :: 
          $Is(s#2, Tclass._module.Stream(_module._default.AlwaysTrue#$_T0))
               && ORD#Less(_k'#2, _k#0)
             ==> _module.__default.True_h(_module._default.AlwaysTrue#$_T0, $LS($LZ), _k'#2, s#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(67,15)"} true;
    }
}



// function declaration for _module._default.AlsoTrue
function _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0: Ty, $ly: LayerType, s#0: DatatypeType) : bool;

function _module.__default.AlsoTrue#canCall(_module._default.AlsoTrue$_T0: Ty, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.AlsoTrue$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $LS($ly), s#0) } 
  _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $LS($ly), s#0)
     == _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $ly, s#0));

// fuel synonym axiom
axiom (forall _module._default.AlsoTrue$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, AsFuelBottom($ly), s#0) } 
  _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $ly, s#0)
     == _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $LZ, s#0));

// consequence axiom for _module.__default.AlsoTrue
axiom 16 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $ly, s#0) } 
    _module.__default.AlsoTrue#canCall(_module._default.AlsoTrue$_T0, s#0)
         || (16 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue$_T0)))
       ==> true);

function _module.__default.AlsoTrue#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.AlsoTrue
axiom (forall _module._default.AlsoTrue$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.AlsoTrue#requires(_module._default.AlsoTrue$_T0, $ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue$_T0))
     ==> _module.__default.AlsoTrue#requires(_module._default.AlsoTrue$_T0, $ly, s#0)
       == true);

// definition axiom for _module.__default.AlsoTrue (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $LS($ly), s#0) } 
    _module.__default.AlsoTrue#canCall(_module._default.AlsoTrue$_T0, s#0)
         || (16 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue$_T0)))
       ==> _module.__default.AlsoTrue#canCall(_module._default.AlsoTrue$_T0, s#0)
         && _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $LS($ly), s#0)
           == _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $ly, s#0));

// 1st prefix predicate axiom for _module.__default.AlsoTrue_h
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.AlsoTrue(_module._default.AlsoTrue#$_T0, $LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue#$_T0))
         && _module.__default.AlsoTrue(_module._default.AlsoTrue#$_T0, $LS($ly), s#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k#0, s#0) } 
        _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k#0, s#0)));

// 2nd prefix predicate axiom
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.AlsoTrue(_module._default.AlsoTrue#$_T0, $LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue#$_T0))
         && (forall _k#0: Box :: 
          { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k#0, s#0) } 
          _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k#0, s#0))
       ==> _module.__default.AlsoTrue(_module._default.AlsoTrue#$_T0, $LS($ly), s#0));

// 3rd prefix predicate axiom
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, s#0: DatatypeType, _k#0: Box :: 
    { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, _k#0, s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue#$_T0))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, _k#0, s#0));

procedure CheckWellformed$$_module.__default.AlsoTrue(_module._default.AlsoTrue$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue$_T0)));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AlsoTrue(_module._default.AlsoTrue$_T0: Ty, s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function AlsoTrue
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(72,19): initial state"} true;
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
        ##s#0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.AlsoTrue$_T0), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.AlsoTrue#canCall(_module._default.AlsoTrue$_T0, s#0);
        assume _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $LS($LZ), s#0)
           == _module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $LS($LZ), s#0);
        assume _module.__default.AlsoTrue#canCall(_module._default.AlsoTrue$_T0, s#0);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.AlsoTrue(_module._default.AlsoTrue$_T0, $LS($LZ), s#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.AlsoTrue#
function _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType)
   : bool;

function _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0: Ty, _k#0: Box, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k#0, s#0) } 
  _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k#0, s#0)
     == _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, _k#0, s#0));

// fuel synonym axiom
axiom (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, AsFuelBottom($ly), _k#0, s#0) } 
  _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, _k#0, s#0)
     == _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LZ, _k#0, s#0));

// consequence axiom for _module.__default.AlsoTrue_h
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, _k#0, s#0) } 
    _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, _k#0, s#0)
         || (17 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue#$_T0)))
       ==> true);

function _module.__default.AlsoTrue_h#requires(Ty, LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.AlsoTrue_h
axiom (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.AlsoTrue_h#requires(_module._default.AlsoTrue#$_T0, $ly, _k#0, s#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue#$_T0))
     ==> _module.__default.AlsoTrue_h#requires(_module._default.AlsoTrue#$_T0, $ly, _k#0, s#0)
       == true);

// definition axiom for _module.__default.AlsoTrue_h (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k#0, s#0) } 
    _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, _k#0, s#0)
         || (17 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, _k'#0, s#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, _k'#0, s#0)))
         && _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k#0, s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, _k'#0, s#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $ly, _k'#0, s#0)))));

// definition axiom for _module.__default.AlsoTrue_h for decreasing-related literals (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), Lit(_k#0), s#0) } 
    _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, Lit(_k#0), s#0)
         || (17 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k'#1, s#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, _k'#1, s#0)))
         && _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), Lit(_k#0), s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k'#1, s#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k'#1, s#0)))));

// definition axiom for _module.__default.AlsoTrue_h for all literals (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall _module._default.AlsoTrue#$_T0: Ty, $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), Lit(_k#0), Lit(s#0)) } 
    _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, Lit(_k#0), Lit(s#0))
         || (17 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.AlsoTrue#$_T0)))
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k'#2, s#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.AlsoTrue_h#canCall(_module._default.AlsoTrue#$_T0, _k'#2, s#0)))
         && _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), Lit(_k#0), Lit(s#0))
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), s#0))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k'#2, s#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.AlsoTrue_h(_module._default.AlsoTrue#$_T0, $LS($ly), _k'#2, s#0)))));

procedure CheckWellformed$$_module.__default.AlsoAlwaysTrue(_module._default.AlsoAlwaysTrue$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.AlsoAlwaysTrue$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.AlsoAlwaysTrue$_T0), $Heap)
         && $IsA#_module.Stream(s#0));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AlsoAlwaysTrue(_module._default.AlsoAlwaysTrue$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.AlsoAlwaysTrue$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.AlsoAlwaysTrue$_T0), $Heap)
         && $IsA#_module.Stream(s#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AlsoTrue#canCall(_module._default.AlsoAlwaysTrue$_T0, s#0);
  free ensures _module.__default.AlsoTrue#canCall(_module._default.AlsoAlwaysTrue$_T0, s#0)
     && 
    _module.__default.AlsoTrue(_module._default.AlsoAlwaysTrue$_T0, $LS($LZ), s#0)
     && $Is(s#0, Tclass._module.Stream(_module._default.AlsoAlwaysTrue$_T0))
     && _module.__default.AlsoTrue(_module._default.AlsoAlwaysTrue$_T0, $LS($LZ), s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} CoCall$$_module.__default.AlsoAlwaysTrue_h(_module._default.AlsoAlwaysTrue#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.AlsoAlwaysTrue#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.AlsoAlwaysTrue#$_T0), $Heap)
         && $IsA#_module.Stream(s#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AlsoTrue_h#canCall(_module._default.AlsoAlwaysTrue#$_T0, _k#0, s#1);
  free ensures _module.__default.AlsoTrue_h#canCall(_module._default.AlsoAlwaysTrue#$_T0, _k#0, s#1)
     && 
    _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LZ), _k#0, s#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, 
        $LS($LZ), 
        ORD#Minus(_k#0, ORD#FromNat(1)), 
        s#1))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LZ), _k'#0, s#1) } 
        ORD#Less(_k'#0, _k#0)
           ==> _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LZ), _k'#0, s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} Impl$$_module.__default.AlsoAlwaysTrue_h(_module._default.AlsoAlwaysTrue#$_T0: Ty, 
    _k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(_module._default.AlsoAlwaysTrue#$_T0))
         && $IsAlloc(s#1, Tclass._module.Stream(_module._default.AlsoAlwaysTrue#$_T0), $Heap)
         && $IsA#_module.Stream(s#1))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AlsoTrue_h#canCall(_module._default.AlsoAlwaysTrue#$_T0, _k#0, s#1);
  ensures _module.__default.AlsoTrue_h#canCall(_module._default.AlsoAlwaysTrue#$_T0, _k#0, s#1)
     ==> _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LZ), _k#0, s#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, 
          $LS($LS($LZ)), 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          s#1));
  ensures _module.__default.AlsoTrue_h#canCall(_module._default.AlsoAlwaysTrue#$_T0, _k#0, s#1)
     ==> _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LZ), _k#0, s#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LS($LZ)), _k'#1, s#1) } 
          ORD#Less(_k'#1, _k#0)
             ==> _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LS($LZ)), _k'#1, s#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1} Impl$$_module.__default.AlsoAlwaysTrue_h(_module._default.AlsoAlwaysTrue#$_T0: Ty, _k#0: Box, s#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: AlsoAlwaysTrue#, Impl$$_module.__default.AlsoAlwaysTrue_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(77,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.AlsoAlwaysTrue#$_T0))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LZ), $ih#_k0#0, $ih#s0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(79,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(77,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, s#2: DatatypeType :: 
          $Is(s#2, Tclass._module.Stream(_module._default.AlsoAlwaysTrue#$_T0))
               && ORD#Less(_k'#2, _k#0)
             ==> _module.__default.AlsoTrue_h(_module._default.AlsoAlwaysTrue#$_T0, $LS($LZ), _k'#2, s#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(77,15)"} true;
    }
}



// function declaration for _module._default.TT
function _module.__default.TT($ly: LayerType, y#0: int) : bool;

function _module.__default.TT#canCall(y#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, y#0: int :: 
  { _module.__default.TT($LS($ly), y#0) } 
  _module.__default.TT($LS($ly), y#0) == _module.__default.TT($ly, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, y#0: int :: 
  { _module.__default.TT(AsFuelBottom($ly), y#0) } 
  _module.__default.TT($ly, y#0) == _module.__default.TT($LZ, y#0));

// consequence axiom for _module.__default.TT
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, y#0: int :: 
    { _module.__default.TT($ly, y#0) } 
    _module.__default.TT#canCall(y#0) || 20 != $FunctionContextHeight ==> true);

function _module.__default.TT#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.TT
axiom (forall $ly: LayerType, y#0: int :: 
  { _module.__default.TT#requires($ly, y#0) } 
  _module.__default.TT#requires($ly, y#0) == true);

// definition axiom for _module.__default.TT (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, y#0: int :: 
    { _module.__default.TT($LS($ly), y#0) } 
    _module.__default.TT#canCall(y#0) || 20 != $FunctionContextHeight
       ==> _module.__default.TT#canCall(y#0 + 1)
         && _module.__default.TT($LS($ly), y#0) == _module.__default.TT($ly, y#0 + 1));

// 1st prefix predicate axiom for _module.__default.TT_h
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, y#0: int :: 
    { _module.__default.TT($LS($ly), y#0) } 
    _module.__default.TT($LS($ly), y#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.TT_h($LS($ly), _k#0, y#0) } 
        _module.__default.TT_h($LS($ly), _k#0, y#0)));

// 2nd prefix predicate axiom
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, y#0: int :: 
    { _module.__default.TT($LS($ly), y#0) } 
    (forall _k#0: Box :: 
        { _module.__default.TT_h($LS($ly), _k#0, y#0) } 
        _module.__default.TT_h($LS($ly), _k#0, y#0))
       ==> _module.__default.TT($LS($ly), y#0));

// 3rd prefix predicate axiom
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, y#0: int, _k#0: Box :: 
    { _module.__default.TT_h($ly, _k#0, y#0) } 
    _k#0 == ORD#FromNat(0) ==> _module.__default.TT_h($ly, _k#0, y#0));

procedure CheckWellformed$$_module.__default.TT(y#0: int);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TT(y#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##y#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function TT
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(82,19): initial state"} true;
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
        ##y#0 := y#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##y#0, TInt, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.TT#canCall(y#0 + 1);
        assume _module.__default.TT($LS($LZ), y#0) == _module.__default.TT($LS($LZ), y#0 + 1);
        assume _module.__default.TT#canCall(y#0 + 1);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.TT($LS($LZ), y#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.TT#
function _module.__default.TT_h($ly: LayerType, _k#0: Box, y#0: int) : bool;

function _module.__default.TT_h#canCall(_k#0: Box, y#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, y#0: int :: 
  { _module.__default.TT_h($LS($ly), _k#0, y#0) } 
  _module.__default.TT_h($LS($ly), _k#0, y#0)
     == _module.__default.TT_h($ly, _k#0, y#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, y#0: int :: 
  { _module.__default.TT_h(AsFuelBottom($ly), _k#0, y#0) } 
  _module.__default.TT_h($ly, _k#0, y#0) == _module.__default.TT_h($LZ, _k#0, y#0));

// consequence axiom for _module.__default.TT_h
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, y#0: int :: 
    { _module.__default.TT_h($ly, _k#0, y#0) } 
    _module.__default.TT_h#canCall(_k#0, y#0) || 21 != $FunctionContextHeight
       ==> true);

function _module.__default.TT_h#requires(LayerType, Box, int) : bool;

// #requires axiom for _module.__default.TT_h
axiom (forall $ly: LayerType, _k#0: Box, y#0: int :: 
  { _module.__default.TT_h#requires($ly, _k#0, y#0) } 
  _module.__default.TT_h#requires($ly, _k#0, y#0) == true);

// definition axiom for _module.__default.TT_h (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, y#0: int :: 
    { _module.__default.TT_h($LS($ly), _k#0, y#0) } 
    _module.__default.TT_h#canCall(_k#0, y#0) || 21 != $FunctionContextHeight
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.TT_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.TT_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.TT_h($ly, _k'#0, y#0) } 
            ORD#Less(_k'#0, _k#0) ==> _module.__default.TT_h#canCall(_k'#0, y#0)))
         && _module.__default.TT_h($LS($ly), _k#0, y#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.TT_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.TT_h($ly, _k'#0, y#0) } 
                ORD#Less(_k'#0, _k#0) ==> _module.__default.TT_h($ly, _k'#0, y#0)))));

// definition axiom for _module.__default.TT_h for decreasing-related literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, y#0: int :: 
    {:weight 3} { _module.__default.TT_h($LS($ly), Lit(_k#0), y#0) } 
    _module.__default.TT_h#canCall(Lit(_k#0), y#0) || 21 != $FunctionContextHeight
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.TT_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.TT_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.TT_h($LS($ly), _k'#1, y#0) } 
            ORD#Less(_k'#1, _k#0) ==> _module.__default.TT_h#canCall(_k'#1, y#0)))
         && _module.__default.TT_h($LS($ly), Lit(_k#0), y#0)
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.TT_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.TT_h($LS($ly), _k'#1, y#0) } 
                ORD#Less(_k'#1, _k#0) ==> _module.__default.TT_h($LS($ly), _k'#1, y#0)))));

// definition axiom for _module.__default.TT_h for all literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, y#0: int :: 
    {:weight 3} { _module.__default.TT_h($LS($ly), Lit(_k#0), LitInt(y#0)) } 
    _module.__default.TT_h#canCall(Lit(_k#0), LitInt(y#0))
         || 21 != $FunctionContextHeight
       ==> (0 < ORD#Offset(_k#0)
           ==> _module.__default.TT_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
         && (
          (0 < ORD#Offset(_k#0)
           ==> _module.__default.TT_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.TT_h($LS($ly), _k'#2, y#0) } 
            ORD#Less(_k'#2, _k#0) ==> _module.__default.TT_h#canCall(_k'#2, y#0)))
         && _module.__default.TT_h($LS($ly), Lit(_k#0), LitInt(y#0))
           == ((0 < ORD#Offset(_k#0)
               ==> _module.__default.TT_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), y#0 + 1))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.TT_h($LS($ly), _k'#2, y#0) } 
                ORD#Less(_k'#2, _k#0) ==> _module.__default.TT_h($LS($ly), _k'#2, y#0)))));

procedure CheckWellformed$$_module.__default.AlwaysTT(y#0: int);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.AlwaysTT(y#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.TT#canCall(y#0);
  free ensures _module.__default.TT#canCall(y#0)
     && 
    _module.__default.TT($LS($LZ), y#0)
     && _module.__default.TT($LS($LZ), y#0 + 1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, y#1} CoCall$$_module.__default.AlwaysTT_h(_k#0: Box, y#1: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.TT_h#canCall(_k#0, y#1);
  free ensures _module.__default.TT_h#canCall(_k#0, y#1)
     && 
    _module.__default.TT_h($LS($LZ), _k#0, y#1)
     && 
    (0 < ORD#Offset(_k#0)
       ==> _module.__default.TT_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), y#1 + 1))
     && (LitInt(0) == ORD#Offset(_k#0)
       ==> (forall _k'#0: Box :: 
        { _module.__default.TT_h($LS($LZ), _k'#0, y#1) } 
        ORD#Less(_k'#0, _k#0) ==> _module.__default.TT_h($LS($LZ), _k'#0, y#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, y#1} Impl$$_module.__default.AlwaysTT_h(_k#0: Box, y#1: int) returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.TT_h#canCall(_k#0, y#1);
  ensures _module.__default.TT_h#canCall(_k#0, y#1)
     ==> _module.__default.TT_h($LS($LZ), _k#0, y#1)
       || (0 < ORD#Offset(_k#0)
         ==> _module.__default.TT_h($LS($LS($LZ)), ORD#Minus(_k#0, ORD#FromNat(1)), y#1 + 1));
  ensures _module.__default.TT_h#canCall(_k#0, y#1)
     ==> _module.__default.TT_h($LS($LZ), _k#0, y#1)
       || (LitInt(0) == ORD#Offset(_k#0)
         ==> (forall _k'#1: Box :: 
          { _module.__default.TT_h($LS($LS($LZ)), _k'#1, y#1) } 
          ORD#Less(_k'#1, _k#0) ==> _module.__default.TT_h($LS($LS($LZ)), _k'#1, y#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, y#1} Impl$$_module.__default.AlwaysTT_h(_k#0: Box, y#1: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: AlwaysTT#, Impl$$_module.__default.AlwaysTT_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(87,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#y0#0: int :: 
      Lit(true)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && 0 <= $ih#y0#0 && $ih#y0#0 < y#1))
         ==> _module.__default.TT_h($LS($LZ), $ih#_k0#0, $ih#y0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(89,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(87,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#2: Box, y#2: int :: 
          ORD#Less(_k'#2, _k#0) ==> _module.__default.TT_h($LS($LZ), _k'#2, y#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(87,15)"} true;
    }
}



// function declaration for _module._default.Append
function _module.__default.Append(_module._default.Append$_T0: Ty, 
    $ly: LayerType, 
    M#0: DatatypeType, 
    N#0: DatatypeType)
   : DatatypeType;

function _module.__default.Append#canCall(_module._default.Append$_T0: Ty, M#0: DatatypeType, N#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.Append$_T0: Ty, 
    $ly: LayerType, 
    M#0: DatatypeType, 
    N#0: DatatypeType :: 
  { _module.__default.Append(_module._default.Append$_T0, $LS($ly), M#0, N#0) } 
  _module.__default.Append(_module._default.Append$_T0, $LS($ly), M#0, N#0)
     == _module.__default.Append(_module._default.Append$_T0, $ly, M#0, N#0));

// fuel synonym axiom
axiom (forall _module._default.Append$_T0: Ty, 
    $ly: LayerType, 
    M#0: DatatypeType, 
    N#0: DatatypeType :: 
  { _module.__default.Append(_module._default.Append$_T0, AsFuelBottom($ly), M#0, N#0) } 
  _module.__default.Append(_module._default.Append$_T0, $ly, M#0, N#0)
     == _module.__default.Append(_module._default.Append$_T0, $LZ, M#0, N#0));

// consequence axiom for _module.__default.Append
axiom 31 <= $FunctionContextHeight
   ==> (forall _module._default.Append$_T0: Ty, 
      $ly: LayerType, 
      M#0: DatatypeType, 
      N#0: DatatypeType :: 
    { _module.__default.Append(_module._default.Append$_T0, $ly, M#0, N#0) } 
    _module.__default.Append#canCall(_module._default.Append$_T0, M#0, N#0)
         || (31 != $FunctionContextHeight
           && 
          $Is(M#0, Tclass._module.IList(_module._default.Append$_T0))
           && $Is(N#0, Tclass._module.IList(_module._default.Append$_T0)))
       ==> $Is(_module.__default.Append(_module._default.Append$_T0, $ly, M#0, N#0), 
        Tclass._module.IList(_module._default.Append$_T0)));

function _module.__default.Append#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Append
axiom (forall _module._default.Append$_T0: Ty, 
    $ly: LayerType, 
    M#0: DatatypeType, 
    N#0: DatatypeType :: 
  { _module.__default.Append#requires(_module._default.Append$_T0, $ly, M#0, N#0) } 
  $Is(M#0, Tclass._module.IList(_module._default.Append$_T0))
       && $Is(N#0, Tclass._module.IList(_module._default.Append$_T0))
     ==> _module.__default.Append#requires(_module._default.Append$_T0, $ly, M#0, N#0)
       == true);

// definition axiom for _module.__default.Append (revealed)
axiom 31 <= $FunctionContextHeight
   ==> (forall _module._default.Append$_T0: Ty, 
      $ly: LayerType, 
      M#0: DatatypeType, 
      N#0: DatatypeType :: 
    { _module.__default.Append(_module._default.Append$_T0, $LS($ly), M#0, N#0) } 
    _module.__default.Append#canCall(_module._default.Append$_T0, M#0, N#0)
         || (31 != $FunctionContextHeight
           && 
          $Is(M#0, Tclass._module.IList(_module._default.Append$_T0))
           && $Is(N#0, Tclass._module.IList(_module._default.Append$_T0)))
       ==> (!_module.IList.Nil_q(M#0)
           ==> (var M'#1 := _module.IList.tail(M#0); 
            _module.__default.Append#canCall(_module._default.Append$_T0, M'#1, N#0)))
         && _module.__default.Append(_module._default.Append$_T0, $LS($ly), M#0, N#0)
           == (if _module.IList.Nil_q(M#0)
             then N#0
             else (var M'#0 := _module.IList.tail(M#0); 
              (var x#0 := _module.IList.head(M#0); 
                #_module.IList.ICons(x#0, _module.__default.Append(_module._default.Append$_T0, $ly, M'#0, N#0))))));

procedure CheckWellformed$$_module.__default.Append(_module._default.Append$_T0: Ty, 
    M#0: DatatypeType
       where $Is(M#0, Tclass._module.IList(_module._default.Append$_T0)), 
    N#0: DatatypeType
       where $Is(N#0, Tclass._module.IList(_module._default.Append$_T0)));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Append(_module._default.Append$_T0: Ty, M#0: DatatypeType, N#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var M'#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: Box;
  var let#1#0#0: Box;
  var ##M#0: DatatypeType;
  var ##N#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Append
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(94,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Append(_module._default.Append$_T0, $LS($LZ), M#0, N#0), 
          Tclass._module.IList(_module._default.Append$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (M#0 == #_module.IList.Nil())
        {
            assume _module.__default.Append(_module._default.Append$_T0, $LS($LZ), M#0, N#0) == N#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Append(_module._default.Append$_T0, $LS($LZ), M#0, N#0), 
              Tclass._module.IList(_module._default.Append$_T0));
        }
        else if (M#0 == #_module.IList.ICons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.Append$_T0);
            assume $Is(_mcc#1#0, Tclass._module.IList(_module._default.Append$_T0));
            havoc M'#Z#0;
            assume $Is(M'#Z#0, Tclass._module.IList(_module._default.Append$_T0));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.IList(_module._default.Append$_T0));
            assume M'#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $IsBox(x#Z#0, _module._default.Append$_T0);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, _module._default.Append$_T0);
            assume x#Z#0 == let#1#0#0;
            ##M#0 := M'#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##M#0, Tclass._module.IList(_module._default.Append$_T0), $Heap);
            ##N#0 := N#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##N#0, Tclass._module.IList(_module._default.Append$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.Append#canCall(_module._default.Append$_T0, M'#Z#0, N#0);
            assume _module.__default.Append(_module._default.Append$_T0, $LS($LZ), M#0, N#0)
               == #_module.IList.ICons(x#Z#0, 
                _module.__default.Append(_module._default.Append$_T0, $LS($LZ), M'#Z#0, N#0));
            assume _module.__default.Append#canCall(_module._default.Append$_T0, M'#Z#0, N#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Append(_module._default.Append$_T0, $LS($LZ), M#0, N#0), 
              Tclass._module.IList(_module._default.Append$_T0));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.zeros
function _module.__default.zeros($ly: LayerType) : DatatypeType;

function _module.__default.zeros#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.zeros($LS($ly)) } 
  _module.__default.zeros($LS($ly)) == _module.__default.zeros($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.zeros(AsFuelBottom($ly)) } 
  _module.__default.zeros($ly) == _module.__default.zeros($LZ));

// consequence axiom for _module.__default.zeros
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.zeros($ly) } 
    _module.__default.zeros#canCall() || 27 != $FunctionContextHeight
       ==> $Is(_module.__default.zeros($ly), Tclass._module.IList(TInt)));

function _module.__default.zeros#requires(LayerType) : bool;

// #requires axiom for _module.__default.zeros
axiom (forall $ly: LayerType :: 
  { _module.__default.zeros#requires($ly) } 
  _module.__default.zeros#requires($ly) == true);

// definition axiom for _module.__default.zeros (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.zeros($LS($ly)) } 
    _module.__default.zeros#canCall() || 27 != $FunctionContextHeight
       ==> _module.__default.zeros#canCall()
         && _module.__default.zeros($LS($ly))
           == Lit(#_module.IList.ICons($Box(LitInt(0)), Lit(_module.__default.zeros($ly)))));

procedure CheckWellformed$$_module.__default.zeros();
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.zeros()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function zeros
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(101,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.zeros($LS($LZ)), Tclass._module.IList(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.zeros#canCall();
        assume _module.__default.zeros($LS($LZ))
           == Lit(#_module.IList.ICons($Box(LitInt(0)), Lit(_module.__default.zeros($LS($LZ)))));
        assume _module.__default.zeros#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.zeros($LS($LZ)), Tclass._module.IList(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.ones
function _module.__default.ones($ly: LayerType) : DatatypeType;

function _module.__default.ones#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.ones($LS($ly)) } 
  _module.__default.ones($LS($ly)) == _module.__default.ones($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.ones(AsFuelBottom($ly)) } 
  _module.__default.ones($ly) == _module.__default.ones($LZ));

// consequence axiom for _module.__default.ones
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.ones($ly) } 
    _module.__default.ones#canCall() || 28 != $FunctionContextHeight
       ==> $Is(_module.__default.ones($ly), Tclass._module.IList(TInt)));

function _module.__default.ones#requires(LayerType) : bool;

// #requires axiom for _module.__default.ones
axiom (forall $ly: LayerType :: 
  { _module.__default.ones#requires($ly) } 
  _module.__default.ones#requires($ly) == true);

// definition axiom for _module.__default.ones (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.ones($LS($ly)) } 
    _module.__default.ones#canCall() || 28 != $FunctionContextHeight
       ==> _module.__default.ones#canCall()
         && _module.__default.ones($LS($ly))
           == Lit(#_module.IList.ICons($Box(LitInt(1)), Lit(_module.__default.ones($ly)))));

procedure CheckWellformed$$_module.__default.ones();
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ones()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ones
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(106,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ones($LS($LZ)), Tclass._module.IList(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.ones#canCall();
        assume _module.__default.ones($LS($LZ))
           == Lit(#_module.IList.ICons($Box(LitInt(1)), Lit(_module.__default.ones($LS($LZ)))));
        assume _module.__default.ones#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ones($LS($LZ)), Tclass._module.IList(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.AtMost
function _module.__default.AtMost($ly: LayerType, a#0: DatatypeType, b#0: DatatypeType) : bool;

function _module.__default.AtMost#canCall(a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.AtMost($LS($ly), a#0, b#0) } 
  _module.__default.AtMost($LS($ly), a#0, b#0)
     == _module.__default.AtMost($ly, a#0, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.AtMost(AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.AtMost($ly, a#0, b#0)
     == _module.__default.AtMost($LZ, a#0, b#0));

// consequence axiom for _module.__default.AtMost
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.AtMost($ly, a#0, b#0) } 
    _module.__default.AtMost#canCall(a#0, b#0)
         || (25 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.IList(TInt))
           && $Is(b#0, Tclass._module.IList(TInt)))
       ==> true);

function _module.__default.AtMost#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.AtMost
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.AtMost#requires($ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.IList(TInt)) && $Is(b#0, Tclass._module.IList(TInt))
     ==> _module.__default.AtMost#requires($ly, a#0, b#0) == true);

// definition axiom for _module.__default.AtMost (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.AtMost($LS($ly), a#0, b#0) } 
    _module.__default.AtMost#canCall(a#0, b#0)
         || (25 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.IList(TInt))
           && $Is(b#0, Tclass._module.IList(TInt)))
       ==> (!_module.IList.Nil_q(a#0)
           ==> (var t#1 := _module.IList.tail(a#0); 
            (var h#1 := $Unbox(_module.IList.head(a#0)): int; 
              _module.IList.ICons_q(b#0)
                 ==> 
                h#1 <= $Unbox(_module.IList.head(b#0)): int
                 ==> _module.__default.AtMost#canCall(t#1, _module.IList.tail(b#0)))))
         && _module.__default.AtMost($LS($ly), a#0, b#0)
           == (if _module.IList.Nil_q(a#0)
             then true
             else (var t#0 := _module.IList.tail(a#0); 
              (var h#0 := $Unbox(_module.IList.head(a#0)): int; 
                _module.IList.ICons_q(b#0)
                   && h#0 <= $Unbox(_module.IList.head(b#0)): int
                   && _module.__default.AtMost($ly, t#0, _module.IList.tail(b#0))))));

// 1st prefix predicate axiom for _module.__default.AtMost_h
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.AtMost($LS($ly), a#0, b#0) } 
    $Is(a#0, Tclass._module.IList(TInt))
         && $Is(b#0, Tclass._module.IList(TInt))
         && _module.__default.AtMost($LS($ly), a#0, b#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.AtMost_h($LS($ly), _k#0, a#0, b#0) } 
        _module.__default.AtMost_h($LS($ly), _k#0, a#0, b#0)));

// 2nd prefix predicate axiom
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.AtMost($LS($ly), a#0, b#0) } 
    $Is(a#0, Tclass._module.IList(TInt))
         && $Is(b#0, Tclass._module.IList(TInt))
         && (forall _k#0: Box :: 
          { _module.__default.AtMost_h($LS($ly), _k#0, a#0, b#0) } 
          _module.__default.AtMost_h($LS($ly), _k#0, a#0, b#0))
       ==> _module.__default.AtMost($LS($ly), a#0, b#0));

// 3rd prefix predicate axiom
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType, _k#0: Box :: 
    { _module.__default.AtMost_h($ly, _k#0, a#0, b#0) } 
    $Is(a#0, Tclass._module.IList(TInt))
         && $Is(b#0, Tclass._module.IList(TInt))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.AtMost_h($ly, _k#0, a#0, b#0));

procedure CheckWellformed$$_module.__default.AtMost(a#0: DatatypeType where $Is(a#0, Tclass._module.IList(TInt)), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.IList(TInt)));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AtMost(a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var t#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var h#Z#0: int;
  var let#1#0#0: int;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function AtMost
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(111,19): initial state"} true;
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
        if (a#0 == #_module.IList.Nil())
        {
            assume _module.__default.AtMost($LS($LZ), a#0, b#0) == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.AtMost($LS($LZ), a#0, b#0), TBool);
        }
        else if (a#0 == #_module.IList.ICons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.IList(TInt));
            havoc t#Z#0;
            assume $Is(t#Z#0, Tclass._module.IList(TInt));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.IList(TInt));
            assume t#Z#0 == let#0#0#0;
            havoc h#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume h#Z#0 == let#1#0#0;
            if (_module.IList.ICons_q(b#0))
            {
                assert _module.IList.ICons_q(b#0);
            }

            if (_module.IList.ICons_q(b#0) && h#Z#0 <= $Unbox(_module.IList.head(b#0)): int)
            {
                assert _module.IList.ICons_q(b#0);
                ##a#0 := t#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##a#0, Tclass._module.IList(TInt), $Heap);
                ##b#0 := _module.IList.tail(b#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##b#0, Tclass._module.IList(TInt), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.AtMost#canCall(t#Z#0, _module.IList.tail(b#0));
            }

            assume _module.__default.AtMost($LS($LZ), a#0, b#0)
               == (
                _module.IList.ICons_q(b#0)
                 && h#Z#0 <= $Unbox(_module.IList.head(b#0)): int
                 && _module.__default.AtMost($LS($LZ), t#Z#0, _module.IList.tail(b#0)));
            assume _module.IList.ICons_q(b#0)
               ==> 
              h#Z#0 <= $Unbox(_module.IList.head(b#0)): int
               ==> _module.__default.AtMost#canCall(t#Z#0, _module.IList.tail(b#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.AtMost($LS($LZ), a#0, b#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.AtMost#
function _module.__default.AtMost_h($ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType) : bool;

function _module.__default.AtMost_h#canCall(_k#0: Box, a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.AtMost_h($LS($ly), _k#0, a#0, b#0) } 
  _module.__default.AtMost_h($LS($ly), _k#0, a#0, b#0)
     == _module.__default.AtMost_h($ly, _k#0, a#0, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.AtMost_h(AsFuelBottom($ly), _k#0, a#0, b#0) } 
  _module.__default.AtMost_h($ly, _k#0, a#0, b#0)
     == _module.__default.AtMost_h($LZ, _k#0, a#0, b#0));

// consequence axiom for _module.__default.AtMost_h
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.AtMost_h($ly, _k#0, a#0, b#0) } 
    _module.__default.AtMost_h#canCall(_k#0, a#0, b#0)
         || (26 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.IList(TInt))
           && $Is(b#0, Tclass._module.IList(TInt)))
       ==> true);

function _module.__default.AtMost_h#requires(LayerType, Box, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.AtMost_h
axiom (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.AtMost_h#requires($ly, _k#0, a#0, b#0) } 
  $Is(a#0, Tclass._module.IList(TInt)) && $Is(b#0, Tclass._module.IList(TInt))
     ==> _module.__default.AtMost_h#requires($ly, _k#0, a#0, b#0) == true);

// definition axiom for _module.__default.AtMost_h (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.AtMost_h($LS($ly), _k#0, a#0, b#0) } 
    _module.__default.AtMost_h#canCall(_k#0, a#0, b#0)
         || (26 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.IList(TInt))
           && $Is(b#0, Tclass._module.IList(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.IList.Nil_q(a#0)
           ==> (var t#3 := _module.IList.tail(a#0); 
            (var h#3 := $Unbox(_module.IList.head(a#0)): int; 
              _module.IList.ICons_q(b#0)
                 ==> 
                h#3 <= $Unbox(_module.IList.head(b#0)): int
                 ==> _module.__default.AtMost_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), t#3, _module.IList.tail(b#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.IList.Nil_q(a#0)
             then true
             else (var t#4 := _module.IList.tail(a#0); 
              (var h#4 := $Unbox(_module.IList.head(a#0)): int; 
                _module.IList.ICons_q(b#0)
                   && h#4 <= $Unbox(_module.IList.head(b#0)): int
                   && _module.__default.AtMost_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), t#4, _module.IList.tail(b#0))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.AtMost_h($ly, _k'#0, a#0, b#0) } 
            ORD#Less(_k'#0, _k#0) ==> _module.__default.AtMost_h#canCall(_k'#0, a#0, b#0)))
         && _module.__default.AtMost_h($LS($ly), _k#0, a#0, b#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.IList.Nil_q(a#0)
                 then true
                 else (var t#2 := _module.IList.tail(a#0); 
                  (var h#2 := $Unbox(_module.IList.head(a#0)): int; 
                    _module.IList.ICons_q(b#0)
                       && h#2 <= $Unbox(_module.IList.head(b#0)): int
                       && _module.__default.AtMost_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), t#2, _module.IList.tail(b#0))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.AtMost_h($ly, _k'#0, a#0, b#0) } 
                ORD#Less(_k'#0, _k#0) ==> _module.__default.AtMost_h($ly, _k'#0, a#0, b#0)))));

// definition axiom for _module.__default.AtMost_h for decreasing-related literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.AtMost_h($LS($ly), Lit(_k#0), a#0, b#0) } 
    _module.__default.AtMost_h#canCall(Lit(_k#0), a#0, b#0)
         || (26 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.IList(TInt))
           && $Is(b#0, Tclass._module.IList(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.IList.Nil_q(a#0)
           ==> (var t#6 := _module.IList.tail(a#0); 
            (var h#6 := $Unbox(_module.IList.head(a#0)): int; 
              _module.IList.ICons_q(b#0)
                 ==> 
                h#6 <= $Unbox(_module.IList.head(b#0)): int
                 ==> _module.__default.AtMost_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), t#6, _module.IList.tail(b#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.IList.Nil_q(a#0)
             then true
             else (var t#7 := _module.IList.tail(a#0); 
              (var h#7 := $Unbox(_module.IList.head(a#0)): int; 
                _module.IList.ICons_q(b#0)
                   && h#7 <= $Unbox(_module.IList.head(b#0)): int
                   && _module.__default.AtMost_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), t#7, _module.IList.tail(b#0))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.AtMost_h($LS($ly), _k'#1, a#0, b#0) } 
            ORD#Less(_k'#1, _k#0) ==> _module.__default.AtMost_h#canCall(_k'#1, a#0, b#0)))
         && _module.__default.AtMost_h($LS($ly), Lit(_k#0), a#0, b#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.IList.Nil_q(a#0)
                 then true
                 else (var t#5 := _module.IList.tail(a#0); 
                  (var h#5 := $Unbox(_module.IList.head(a#0)): int; 
                    _module.IList.ICons_q(b#0)
                       && h#5 <= $Unbox(_module.IList.head(b#0)): int
                       && _module.__default.AtMost_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), t#5, _module.IList.tail(b#0))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.AtMost_h($LS($ly), _k'#1, a#0, b#0) } 
                ORD#Less(_k'#1, _k#0) ==> _module.__default.AtMost_h($LS($ly), _k'#1, a#0, b#0)))));

// definition axiom for _module.__default.AtMost_h for all literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, a#0: DatatypeType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.AtMost_h($LS($ly), Lit(_k#0), Lit(a#0), Lit(b#0)) } 
    _module.__default.AtMost_h#canCall(Lit(_k#0), Lit(a#0), Lit(b#0))
         || (26 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.IList(TInt))
           && $Is(b#0, Tclass._module.IList(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.IList.Nil_q(a#0)
           ==> (var t#9 := _module.IList.tail(a#0); 
            (var h#9 := $Unbox(_module.IList.head(a#0)): int; 
              _module.IList.ICons_q(b#0)
                 ==> 
                h#9 <= $Unbox(_module.IList.head(b#0)): int
                 ==> _module.__default.AtMost_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), t#9, _module.IList.tail(b#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.IList.Nil_q(a#0)
             then true
             else (var t#10 := _module.IList.tail(a#0); 
              (var h#10 := $Unbox(_module.IList.head(a#0)): int; 
                _module.IList.ICons_q(b#0)
                   && h#10 <= $Unbox(_module.IList.head(b#0)): int
                   && _module.__default.AtMost_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), t#10, _module.IList.tail(b#0))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.AtMost_h($LS($ly), _k'#2, a#0, b#0) } 
            ORD#Less(_k'#2, _k#0) ==> _module.__default.AtMost_h#canCall(_k'#2, a#0, b#0)))
         && _module.__default.AtMost_h($LS($ly), Lit(_k#0), Lit(a#0), Lit(b#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.IList.Nil_q(a#0)
                 then true
                 else (var t#8 := _module.IList.tail(a#0); 
                  (var h#8 := $Unbox(_module.IList.head(a#0)): int; 
                    _module.IList.ICons_q(b#0)
                       && h#8 <= $Unbox(_module.IList.head(b#0)): int
                       && _module.__default.AtMost_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), t#8, _module.IList.tail(b#0))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.AtMost_h($LS($ly), _k'#2, a#0, b#0) } 
                ORD#Less(_k'#2, _k#0) ==> _module.__default.AtMost_h($LS($ly), _k'#2, a#0, b#0)))));

procedure CheckWellformed$$_module.__default.ZerosAndOnes__Theorem0();
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ZerosAndOnes__Theorem0();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.zeros#canCall()
     && _module.__default.ones#canCall()
     && _module.__default.AtMost#canCall(Lit(_module.__default.zeros($LS($LZ))), Lit(_module.__default.ones($LS($LZ))));
  ensures Lit(_module.__default.AtMost($LS($LS($LZ)), 
      Lit(_module.__default.zeros($LS($LS($LZ)))), 
      Lit(_module.__default.ones($LS($LS($LZ))))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} CoCall$$_module.__default.ZerosAndOnes__Theorem0_h(_k#0: Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.zeros#canCall()
     && _module.__default.ones#canCall()
     && _module.__default.AtMost_h#canCall(_k#0, 
      Lit(_module.__default.zeros($LS($LZ))), 
      Lit(_module.__default.ones($LS($LZ))));
  ensures _module.__default.AtMost_h($LS($LS($LZ)), 
    _k#0, 
    Lit(_module.__default.zeros($LS($LS($LZ)))), 
    Lit(_module.__default.ones($LS($LS($LZ)))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} Impl$$_module.__default.ZerosAndOnes__Theorem0_h(_k#0: Box) returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.zeros#canCall()
     && _module.__default.ones#canCall()
     && _module.__default.AtMost_h#canCall(_k#0, 
      Lit(_module.__default.zeros($LS($LZ))), 
      Lit(_module.__default.ones($LS($LZ))));
  ensures _module.__default.AtMost_h($LS($LS($LZ)), 
    _k#0, 
    Lit(_module.__default.zeros($LS($LS($LZ)))), 
    Lit(_module.__default.ones($LS($LS($LZ)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0} Impl$$_module.__default.ZerosAndOnes__Theorem0_h(_k#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: ZerosAndOnes_Theorem0#, Impl$$_module.__default.ZerosAndOnes__Theorem0_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(118,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box :: 
      Lit(true) && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.AtMost_h($LS($LZ), 
          $ih#_k0#0, 
          Lit(_module.__default.zeros($LS($LZ))), 
          Lit(_module.__default.ones($LS($LZ)))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(120,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(118,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box :: 
          ORD#Less(_k'#0, _k#0)
             ==> _module.__default.AtMost_h($LS($LZ), 
              _k'#0, 
              Lit(_module.__default.zeros($LS($LZ))), 
              Lit(_module.__default.ones($LS($LZ)))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(118,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.ZerosAndOnes__Theorem1();
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ZerosAndOnes__Theorem1();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.IList(Lit(_module.__default.Append(TInt, 
          $LS($LZ), 
          Lit(_module.__default.zeros($LS($LZ))), 
          Lit(_module.__default.ones($LS($LZ))))))
     && $IsA#_module.IList(Lit(_module.__default.zeros($LS($LZ))))
     && 
    _module.__default.zeros#canCall()
     && _module.__default.ones#canCall()
     && _module.__default.Append#canCall(TInt, 
      Lit(_module.__default.zeros($LS($LZ))), 
      Lit(_module.__default.ones($LS($LZ))))
     && _module.__default.zeros#canCall();
  ensures $Eq#_module.IList(TInt, 
    TInt, 
    $LS($LS($LZ)), 
    _module.__default.Append(TInt, 
      $LS($LS($LZ)), 
      Lit(_module.__default.zeros($LS($LS($LZ)))), 
      Lit(_module.__default.ones($LS($LS($LZ))))), 
    _module.__default.zeros($LS($LS($LZ))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} CoCall$$_module.__default.ZerosAndOnes__Theorem1_h(_k#0: Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.zeros#canCall()
     && _module.__default.ones#canCall()
     && _module.__default.Append#canCall(TInt, 
      Lit(_module.__default.zeros($LS($LZ))), 
      Lit(_module.__default.ones($LS($LZ))))
     && _module.__default.zeros#canCall();
  free ensures $PrefixEq#_module.IList(TInt, 
    TInt, 
    _k#0, 
    $LS($LS($LZ)), 
    Lit(_module.__default.Append(TInt, 
        $LS($LZ), 
        Lit(_module.__default.zeros($LS($LZ))), 
        Lit(_module.__default.ones($LS($LZ))))), 
    Lit(_module.__default.zeros($LS($LZ))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} Impl$$_module.__default.ZerosAndOnes__Theorem1_h(_k#0: Box) returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.zeros#canCall()
     && _module.__default.ones#canCall()
     && _module.__default.Append#canCall(TInt, 
      Lit(_module.__default.zeros($LS($LZ))), 
      Lit(_module.__default.ones($LS($LZ))))
     && _module.__default.zeros#canCall();
  ensures $PrefixEq#_module.IList(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      Lit(_module.__default.Append(TInt, 
          $LS($LZ), 
          Lit(_module.__default.zeros($LS($LZ))), 
          Lit(_module.__default.ones($LS($LZ))))), 
      Lit(_module.__default.zeros($LS($LZ))))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.IList.Nil_q(Lit(_module.__default.Append(TInt, 
            $LS($LS($LZ)), 
            Lit(_module.__default.zeros($LS($LS($LZ)))), 
            Lit(_module.__default.ones($LS($LS($LZ)))))))
       ==> _module.IList.Nil_q(Lit(_module.__default.zeros($LS($LS($LZ))))));
  ensures $PrefixEq#_module.IList(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      Lit(_module.__default.Append(TInt, 
          $LS($LZ), 
          Lit(_module.__default.zeros($LS($LZ))), 
          Lit(_module.__default.ones($LS($LZ))))), 
      Lit(_module.__default.zeros($LS($LZ))))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.IList.ICons_q(Lit(_module.__default.Append(TInt, 
            $LS($LS($LZ)), 
            Lit(_module.__default.zeros($LS($LS($LZ)))), 
            Lit(_module.__default.ones($LS($LS($LZ)))))))
       ==> _module.IList.ICons_q(Lit(_module.__default.zeros($LS($LS($LZ)))))
         && 
        $Unbox(_module.IList.head(Lit(_module.__default.Append(TInt, 
                  $LS($LS($LZ)), 
                  Lit(_module.__default.zeros($LS($LS($LZ)))), 
                  Lit(_module.__default.ones($LS($LS($LZ)))))))): int
           == $Unbox(_module.IList.head(Lit(_module.__default.zeros($LS($LS($LZ)))))): int
         && $PrefixEq#_module.IList(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.IList.tail(Lit(_module.__default.Append(TInt, 
                $LS($LS($LZ)), 
                Lit(_module.__default.zeros($LS($LS($LZ)))), 
                Lit(_module.__default.ones($LS($LS($LZ))))))), 
          _module.IList.tail(Lit(_module.__default.zeros($LS($LS($LZ)))))));
  ensures $PrefixEq#_module.IList(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      Lit(_module.__default.Append(TInt, 
          $LS($LZ), 
          Lit(_module.__default.zeros($LS($LZ))), 
          Lit(_module.__default.ones($LS($LZ))))), 
      Lit(_module.__default.zeros($LS($LZ))))
     || 
    (0 < ORD#Offset(_k#0)
       ==> (_module.IList.Nil_q(Lit(_module.__default.Append(TInt, 
                $LS($LS($LZ)), 
                Lit(_module.__default.zeros($LS($LS($LZ)))), 
                Lit(_module.__default.ones($LS($LS($LZ)))))))
           ==> _module.IList.Nil_q(Lit(_module.__default.zeros($LS($LS($LZ))))))
         && (_module.IList.ICons_q(Lit(_module.__default.Append(TInt, 
                $LS($LS($LZ)), 
                Lit(_module.__default.zeros($LS($LS($LZ)))), 
                Lit(_module.__default.ones($LS($LS($LZ)))))))
           ==> _module.IList.ICons_q(Lit(_module.__default.zeros($LS($LS($LZ)))))
             && 
            $Unbox(_module.IList.head(Lit(_module.__default.Append(TInt, 
                      $LS($LS($LZ)), 
                      Lit(_module.__default.zeros($LS($LS($LZ)))), 
                      Lit(_module.__default.ones($LS($LS($LZ)))))))): int
               == $Unbox(_module.IList.head(Lit(_module.__default.zeros($LS($LS($LZ)))))): int
             && $PrefixEq#_module.IList(TInt, 
              TInt, 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              $LS($LS($LZ)), 
              _module.IList.tail(Lit(_module.__default.Append(TInt, 
                    $LS($LS($LZ)), 
                    Lit(_module.__default.zeros($LS($LS($LZ)))), 
                    Lit(_module.__default.ones($LS($LS($LZ))))))), 
              _module.IList.tail(Lit(_module.__default.zeros($LS($LS($LZ))))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.IList(TInt, 
        TInt, 
        $LS($LS($LZ)), 
        Lit(_module.__default.Append(TInt, 
            $LS($LZ), 
            Lit(_module.__default.zeros($LS($LZ))), 
            Lit(_module.__default.ones($LS($LZ))))), 
        Lit(_module.__default.zeros($LS($LZ)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0} Impl$$_module.__default.ZerosAndOnes__Theorem1_h(_k#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: ZerosAndOnes_Theorem1#, Impl$$_module.__default.ZerosAndOnes__Theorem1_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(123,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box :: 
      Lit(true) && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.IList(TInt, 
          TInt, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          Lit(_module.__default.Append(TInt, 
              $LS($LZ), 
              Lit(_module.__default.zeros($LS($LZ))), 
              Lit(_module.__default.ones($LS($LZ))))), 
          Lit(_module.__default.zeros($LS($LZ)))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(125,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(123,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box :: 
          ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.IList(TInt, 
              TInt, 
              _k'#0, 
              $LS($LS($LZ)), 
              Lit(_module.__default.Append(TInt, 
                  $LS($LZ), 
                  Lit(_module.__default.zeros($LS($LZ))), 
                  Lit(_module.__default.ones($LS($LZ))))), 
              Lit(_module.__default.zeros($LS($LZ)))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/SimpleCoinduction.dfy(123,15)"} true;
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

const unique tytagFamily$IList: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
