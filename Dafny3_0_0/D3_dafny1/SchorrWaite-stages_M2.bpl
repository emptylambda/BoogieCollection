// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy -print:./SchorrWaite-stages.bpl

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

function Tclass._System.___hFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hFunc4: TyTag;

// Tclass._System.___hFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tag(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hFunc4
     && TagFamily(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#Func4);

// Tclass._System.___hFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_0(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hFunc4_0(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_1(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hFunc4_1(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_2(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hFunc4_2(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_3(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hFunc4_3(Ty) : Ty;

// Tclass._System.___hFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hFunc4_4(Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

function Tclass._System.___hFunc4_4(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $IsBox(bx, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

function Handle4([Heap,Box,Box,Box,Box]Box, 
    [Heap,Box,Box,Box,Box]bool, 
    [Heap,Box,Box,Box,Box]Set Box)
   : HandleType;

function Apply4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : Box;

function Requires4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : bool;

function Reads4(Ty, Ty, Ty, Ty, Ty, Heap, HandleType, Box, Box, Box, Box) : Set Box;

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { Apply4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3) } 
  Apply4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)
     == h[heap, bx0, bx1, bx2, bx3]);

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { Requires4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3) } 
  r[heap, bx0, bx1, bx2, bx3]
     ==> Requires4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3));

axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    h: [Heap,Box,Box,Box,Box]Box, 
    r: [Heap,Box,Box,Box,Box]bool, 
    rd: [Heap,Box,Box,Box,Box]Set Box, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box, 
    bx: Box :: 
  { Reads4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)[bx] } 
  Reads4(t0, t1, t2, t3, t4, heap, Handle4(h, r, rd), bx0, bx1, bx2, bx3)[bx]
     == rd[heap, bx0, bx1, bx2, bx3][bx]);

function {:inline} Requires4#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box)
   : bool
{
  true
}

function {:inline} Reads4#canCall(t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box)
   : bool
{
  true
}

// frame axiom for Reads4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Reads4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Requires4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Requires4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Requires4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Apply4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// frame axiom for Apply4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    h0: Heap, 
    h1: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { $HeapSucc(h0, h1), Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3) } 
  $HeapSucc(h0, h1)
       && 
      $IsGoodHeap(h0)
       && $IsGoodHeap(h1)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && (forall<a> o: ref, fld: Field a :: 
        o != null && Reads4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3)[$Box(o)]
           ==> read(h0, o, fld) == read(h1, o, fld))
     ==> Apply4(t0, t1, t2, t3, t4, h0, f, bx0, bx1, bx2, bx3)
       == Apply4(t0, t1, t2, t3, t4, h1, f, bx0, bx1, bx2, bx3));

// empty-reads property for Reads4 
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), $IsGoodHeap(heap) } 
    { Reads4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
     ==> (Set#Equal(Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), 
        Set#Empty(): Set Box)
       <==> Set#Equal(Reads4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3), Set#Empty(): Set Box)));

// empty-reads property for Requires4
axiom (forall t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    heap: Heap, 
    f: HandleType, 
    bx0: Box, 
    bx1: Box, 
    bx2: Box, 
    bx3: Box :: 
  { Requires4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), $IsGoodHeap(heap) } 
    { Requires4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3) } 
  $IsGoodHeap(heap)
       && 
      $IsBox(bx0, t0)
       && $IsBox(bx1, t1)
       && $IsBox(bx2, t2)
       && $IsBox(bx3, t3)
       && $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
       && Set#Equal(Reads4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3), 
        Set#Empty(): Set Box)
     ==> Requires4(t0, t1, t2, t3, t4, $OneHeap, f, bx0, bx1, bx2, bx3)
       == Requires4(t0, t1, t2, t3, t4, heap, f, bx0, bx1, bx2, bx3));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty :: 
  { $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4)) } 
  $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
     <==> (forall h: Heap, bx0: Box, bx1: Box, bx2: Box, bx3: Box :: 
      { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) } 
      $IsGoodHeap(h)
           && 
          $IsBox(bx0, t0)
           && $IsBox(bx1, t1)
           && $IsBox(bx2, t2)
           && $IsBox(bx3, t3)
           && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
         ==> $IsBox(Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3), t4)));

axiom (forall f: HandleType, 
    t0: Ty, 
    t1: Ty, 
    t2: Ty, 
    t3: Ty, 
    t4: Ty, 
    u0: Ty, 
    u1: Ty, 
    u2: Ty, 
    u3: Ty, 
    u4: Ty :: 
  { $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4)), $Is(f, Tclass._System.___hFunc4(u0, u1, u2, u3, u4)) } 
  $Is(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4))
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
        { $IsBox(bx, u3) } { $IsBox(bx, t3) } 
        $IsBox(bx, u3) ==> $IsBox(bx, t3))
       && (forall bx: Box :: 
        { $IsBox(bx, t4) } { $IsBox(bx, u4) } 
        $IsBox(bx, t4) ==> $IsBox(bx, u4))
     ==> $Is(f, Tclass._System.___hFunc4(u0, u1, u2, u3, u4)));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h) } 
  $IsGoodHeap(h)
     ==> ($IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h)
       <==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box :: 
        { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) } 
          { Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) } 
        $IsBox(bx0, t0)
             && $IsAllocBox(bx0, t0, h)
             && 
            $IsBox(bx1, t1)
             && $IsAllocBox(bx1, t1, h)
             && 
            $IsBox(bx2, t2)
             && $IsAllocBox(bx2, t2, h)
             && 
            $IsBox(bx3, t3)
             && $IsAllocBox(bx3, t3, h)
             && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
           ==> (forall r: ref :: 
            { Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)[$Box(r)] } 
            r != null && Reads4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)[$Box(r)]
               ==> read(h, r, alloc)))));

axiom (forall f: HandleType, t0: Ty, t1: Ty, t2: Ty, t3: Ty, t4: Ty, h: Heap :: 
  { $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h) } 
  $IsGoodHeap(h) && $IsAlloc(f, Tclass._System.___hFunc4(t0, t1, t2, t3, t4), h)
     ==> (forall bx0: Box, bx1: Box, bx2: Box, bx3: Box :: 
      { Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3) } 
      $IsAllocBox(bx0, t0, h)
           && $IsAllocBox(bx1, t1, h)
           && $IsAllocBox(bx2, t2, h)
           && $IsAllocBox(bx3, t3, h)
           && Requires4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3)
         ==> $IsAllocBox(Apply4(t0, t1, t2, t3, t4, h, f, bx0, bx1, bx2, bx3), t4, h)));

function Tclass._System.___hPartialFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hPartialFunc4: TyTag;

// Tclass._System.___hPartialFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tag(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hPartialFunc4
     && TagFamily(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#PartialFunc4);

// Tclass._System.___hPartialFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_0(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hPartialFunc4_0(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_1(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hPartialFunc4_1(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_2(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hPartialFunc4_2(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_3(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hPartialFunc4_3(Ty) : Ty;

// Tclass._System.___hPartialFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hPartialFunc4_4(Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

function Tclass._System.___hPartialFunc4_4(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hPartialFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $IsBox(bx, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

// _System._#PartialFunc4: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     <==> $Is(f#0, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
           ==> Set#Equal(Reads4(#$T0, #$T1, #$T2, #$T3, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0), 
            Set#Empty(): Set Box)));

// _System._#PartialFunc4: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h));

function Tclass._System.___hTotalFunc4(Ty, Ty, Ty, Ty, Ty) : Ty;

const unique Tagclass._System.___hTotalFunc4: TyTag;

// Tclass._System.___hTotalFunc4 Tag
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tag(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == Tagclass._System.___hTotalFunc4
     && TagFamily(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       == tytagFamily$_#TotalFunc4);

// Tclass._System.___hTotalFunc4 injectivity 0
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_0(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T0);

function Tclass._System.___hTotalFunc4_0(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 1
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_1(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T1);

function Tclass._System.___hTotalFunc4_1(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 2
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_2(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T2);

function Tclass._System.___hTotalFunc4_2(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 3
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_3(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$T3);

function Tclass._System.___hTotalFunc4_3(Ty) : Ty;

// Tclass._System.___hTotalFunc4 injectivity 4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty :: 
  { Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R) } 
  Tclass._System.___hTotalFunc4_4(Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     == #$R);

function Tclass._System.___hTotalFunc4_4(Ty) : Ty;

// Box/unbox axiom for Tclass._System.___hTotalFunc4
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $IsBox(bx, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)));

// _System._#TotalFunc4: subset type $Is
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R)) } 
  $Is(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
     <==> $Is(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R))
       && (forall x0#0: Box, x1#0: Box, x2#0: Box, x3#0: Box :: 
        $IsBox(x0#0, #$T0)
             && $IsBox(x1#0, #$T1)
             && $IsBox(x2#0, #$T2)
             && $IsBox(x3#0, #$T3)
           ==> Requires4(#$T0, #$T1, #$T2, #$T3, #$R, $OneHeap, f#0, x0#0, x1#0, x2#0, x3#0)));

// _System._#TotalFunc4: subset type $IsAlloc
axiom (forall #$T0: Ty, #$T1: Ty, #$T2: Ty, #$T3: Ty, #$R: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h) } 
  $IsAlloc(f#0, Tclass._System.___hTotalFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h)
     <==> $IsAlloc(f#0, Tclass._System.___hPartialFunc4(#$T0, #$T1, #$T2, #$T3, #$R), $h));

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

const unique class.M2.Node?: ClassName;

function Tclass.M2.Node?() : Ty;

const unique Tagclass.M2.Node?: TyTag;

// Tclass.M2.Node? Tag
axiom Tag(Tclass.M2.Node?()) == Tagclass.M2.Node?
   && TagFamily(Tclass.M2.Node?()) == tytagFamily$Node;

// Box/unbox axiom for Tclass.M2.Node?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M2.Node?()) } 
  $IsBox(bx, Tclass.M2.Node?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M2.Node?()));

// Node: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M2.Node?()) } 
  $Is($o, Tclass.M2.Node?()) <==> $o == null || dtype($o) == Tclass.M2.Node?());

// Node: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M2.Node?(), $h) } 
  $IsAlloc($o, Tclass.M2.Node?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(M2.Node.pathFromRoot) == 0
   && FieldOfDecl(class.M2.Node?, field$pathFromRoot) == M2.Node.pathFromRoot
   && $IsGhostField(M2.Node.pathFromRoot);

const M2.Node.pathFromRoot: Field DatatypeType;

function Tclass.M2.Path() : Ty;

const unique Tagclass.M2.Path: TyTag;

// Tclass.M2.Path Tag
axiom Tag(Tclass.M2.Path()) == Tagclass.M2.Path
   && TagFamily(Tclass.M2.Path()) == tytagFamily$Path;

// Box/unbox axiom for Tclass.M2.Path
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M2.Path()) } 
  $IsBox(bx, Tclass.M2.Path())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.M2.Path()));

// Node.pathFromRoot: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M2.Node.pathFromRoot) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.M2.Node?()
     ==> $Is(read($h, $o, M2.Node.pathFromRoot), Tclass.M2.Path()));

// Node.pathFromRoot: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M2.Node.pathFromRoot) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.M2.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, M2.Node.pathFromRoot), Tclass.M2.Path(), $h));

axiom FDim(M2.Node.children) == 0
   && FieldOfDecl(class.M2.Node?, field$children) == M2.Node.children
   && !$IsGhostField(M2.Node.children);

const M2.Node.children: Field (Seq Box);

// Node.children: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M2.Node.children) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.M2.Node?()
     ==> $Is(read($h, $o, M2.Node.children), TSeq(Tclass.M2.Node?())));

// Node.children: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M2.Node.children) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.M2.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, M2.Node.children), TSeq(Tclass.M2.Node?()), $h));

axiom FDim(M2.Node.marked) == 0
   && FieldOfDecl(class.M2.Node?, field$marked) == M2.Node.marked
   && !$IsGhostField(M2.Node.marked);

const M2.Node.marked: Field bool;

// Node.marked: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M2.Node.marked) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.M2.Node?()
     ==> $Is(read($h, $o, M2.Node.marked), TBool));

// Node.marked: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M2.Node.marked) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.M2.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, M2.Node.marked), TBool, $h));

axiom FDim(M2.Node.childrenVisited) == 0
   && FieldOfDecl(class.M2.Node?, field$childrenVisited) == M2.Node.childrenVisited
   && !$IsGhostField(M2.Node.childrenVisited);

const M2.Node.childrenVisited: Field int;

// Node.childrenVisited: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M2.Node.childrenVisited) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.M2.Node?()
     ==> $Is(read($h, $o, M2.Node.childrenVisited), Tclass._System.nat()));

// Node.childrenVisited: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M2.Node.childrenVisited) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.M2.Node?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, M2.Node.childrenVisited), Tclass._System.nat(), $h));

function Tclass.M2.Node() : Ty;

const unique Tagclass.M2.Node: TyTag;

// Tclass.M2.Node Tag
axiom Tag(Tclass.M2.Node()) == Tagclass.M2.Node
   && TagFamily(Tclass.M2.Node()) == tytagFamily$Node;

// Box/unbox axiom for Tclass.M2.Node
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M2.Node()) } 
  $IsBox(bx, Tclass.M2.Node())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M2.Node()));

// M2.Node: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.M2.Node()) } 
  $Is(c#0, Tclass.M2.Node()) <==> $Is(c#0, Tclass.M2.Node?()) && c#0 != null);

// M2.Node: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.M2.Node(), $h) } 
  $IsAlloc(c#0, Tclass.M2.Node(), $h) <==> $IsAlloc(c#0, Tclass.M2.Node?(), $h));

const unique class.M2.__default: ClassName;

function Tclass.M2.__default() : Ty;

const unique Tagclass.M2.__default: TyTag;

// Tclass.M2.__default Tag
axiom Tag(Tclass.M2.__default()) == Tagclass.M2.__default
   && TagFamily(Tclass.M2.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.M2.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M2.__default()) } 
  $IsBox(bx, Tclass.M2.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M2.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M2.__default()) } 
  $Is($o, Tclass.M2.__default())
     <==> $o == null || dtype($o) == Tclass.M2.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M2.__default(), $h) } 
  $IsAlloc($o, Tclass.M2.__default(), $h) <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$M2.__default.SchorrWaite(root#0: ref
       where $Is(root#0, Tclass.M2.Node()) && $IsAlloc(root#0, Tclass.M2.Node(), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass.M2.Node())) && $IsAlloc(S#0, TSet(Tclass.M2.Node()), $Heap));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$M2.__default.SchorrWaite(root#0: ref
       where $Is(root#0, Tclass.M2.Node()) && $IsAlloc(root#0, Tclass.M2.Node(), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass.M2.Node())) && $IsAlloc(S#0, TSet(Tclass.M2.Node()), $Heap));
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref :: 
    { read($Heap, n#1, M2.Node.children) } { S#0[$Box(n#1)] } 
    $Is(n#1, Tclass.M2.Node())
       ==> 
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref :: 
        { S#0[$Box(ch#2)] } 
          { Seq#Contains(read($Heap, n#1, M2.Node.children), $Box(ch#2)) } 
        $Is(ch#2, Tclass.M2.Node?())
           ==> 
          Seq#Contains(read($Heap, n#1, M2.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref :: 
    { read($Heap, n#3, M2.Node.childrenVisited) } 
      { read($Heap, n#3, M2.Node.marked) } 
      { S#0[$Box(n#3)] } 
    $Is(n#3, Tclass.M2.Node())
       ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, M2.Node.marked))
         && (S#0[$Box(n#3)] ==> read($Heap, n#3, M2.Node.childrenVisited) == LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, root#0, M2.Node.marked);
  free ensures true;
  ensures (forall n#5: ref :: 
    { read($Heap, n#5, M2.Node.children) } 
      { read($Heap, n#5, M2.Node.marked) } 
      { S#0[$Box(n#5)] } 
    $Is(n#5, Tclass.M2.Node())
       ==> 
      S#0[$Box(n#5)] && read($Heap, n#5, M2.Node.marked)
       ==> (forall ch#5: ref :: 
        { read($Heap, ch#5, M2.Node.marked) } 
          { Seq#Contains(read($Heap, n#5, M2.Node.children), $Box(ch#5)) } 
        $Is(ch#5, Tclass.M2.Node?())
           ==> 
          Seq#Contains(read($Heap, n#5, M2.Node.children), $Box(ch#5)) && ch#5 != null
           ==> read($Heap, ch#5, M2.Node.marked)));
  free ensures (forall n#7: ref :: 
    { M2.__default.Reachable(old($Heap), root#0, n#7, S#0) } 
      { read($Heap, n#7, M2.Node.marked) } 
      { S#0[$Box(n#7)] } 
    $Is(n#7, Tclass.M2.Node())
       ==> 
      S#0[$Box(n#7)]
       ==> 
      read($Heap, n#7, M2.Node.marked)
       ==> M2.__default.Reachable#canCall(old($Heap), root#0, n#7, S#0));
  ensures (forall n#7: ref :: 
    { M2.__default.Reachable(old($Heap), root#0, n#7, S#0) } 
      { read($Heap, n#7, M2.Node.marked) } 
      { S#0[$Box(n#7)] } 
    $Is(n#7, Tclass.M2.Node())
       ==> 
      S#0[$Box(n#7)] && read($Heap, n#7, M2.Node.marked)
       ==> M2.__default.Reachable(old($Heap), root#0, n#7, S#0));
  free ensures true;
  ensures (forall n#9: ref :: 
    { read(old($Heap), n#9, M2.Node.children) } 
      { read($Heap, n#9, M2.Node.children) } 
      { read(old($Heap), n#9, M2.Node.childrenVisited) } 
      { read($Heap, n#9, M2.Node.childrenVisited) } 
      { S#0[$Box(n#9)] } 
    $Is(n#9, Tclass.M2.Node())
       ==> (S#0[$Box(n#9)]
           ==> read($Heap, n#9, M2.Node.childrenVisited)
             == read(old($Heap), n#9, M2.Node.childrenVisited))
         && (S#0[$Box(n#9)]
           ==> Seq#Equal(read($Heap, n#9, M2.Node.children), read(old($Heap), n#9, M2.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$M2.__default.SchorrWaite(root#0: ref
       where $Is(root#0, Tclass.M2.Node()) && $IsAlloc(root#0, Tclass.M2.Node(), $Heap), 
    S#0: Set Box
       where $Is(S#0, TSet(Tclass.M2.Node())) && $IsAlloc(S#0, TSet(Tclass.M2.Node()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  // user-defined preconditions
  requires S#0[$Box(root#0)];
  requires (forall n#1: ref :: 
    { read($Heap, n#1, M2.Node.children) } { S#0[$Box(n#1)] } 
    $Is(n#1, Tclass.M2.Node())
       ==> 
      S#0[$Box(n#1)]
       ==> (forall ch#2: ref :: 
        { S#0[$Box(ch#2)] } 
          { Seq#Contains(read($Heap, n#1, M2.Node.children), $Box(ch#2)) } 
        $Is(ch#2, Tclass.M2.Node?())
           ==> 
          Seq#Contains(read($Heap, n#1, M2.Node.children), $Box(ch#2))
           ==> ch#2 == null || S#0[$Box(ch#2)]));
  requires (forall n#3: ref :: 
    { read($Heap, n#3, M2.Node.childrenVisited) } 
      { read($Heap, n#3, M2.Node.marked) } 
      { S#0[$Box(n#3)] } 
    $Is(n#3, Tclass.M2.Node())
       ==> (S#0[$Box(n#3)] ==> !read($Heap, n#3, M2.Node.marked))
         && (S#0[$Box(n#3)] ==> read($Heap, n#3, M2.Node.childrenVisited) == LitInt(0)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures $_reverifyPost ==> read($Heap, root#0, M2.Node.marked);
  free ensures true;
  ensures $_reverifyPost
     ==> (forall n#5: ref :: 
      { read($Heap, n#5, M2.Node.children) } 
        { read($Heap, n#5, M2.Node.marked) } 
        { S#0[$Box(n#5)] } 
      $Is(n#5, Tclass.M2.Node())
         ==> 
        S#0[$Box(n#5)] && read($Heap, n#5, M2.Node.marked)
         ==> (forall ch#5: ref :: 
          { read($Heap, ch#5, M2.Node.marked) } 
            { Seq#Contains(read($Heap, n#5, M2.Node.children), $Box(ch#5)) } 
          $Is(ch#5, Tclass.M2.Node?())
             ==> 
            Seq#Contains(read($Heap, n#5, M2.Node.children), $Box(ch#5)) && ch#5 != null
             ==> read($Heap, ch#5, M2.Node.marked)));
  free ensures (forall n#7: ref :: 
    { M2.__default.Reachable(old($Heap), root#0, n#7, S#0) } 
      { read($Heap, n#7, M2.Node.marked) } 
      { S#0[$Box(n#7)] } 
    $Is(n#7, Tclass.M2.Node())
       ==> 
      S#0[$Box(n#7)]
       ==> 
      read($Heap, n#7, M2.Node.marked)
       ==> M2.__default.Reachable#canCall(old($Heap), root#0, n#7, S#0));
  ensures $_reverifyPost
     ==> (forall n#7: ref :: 
      { M2.__default.Reachable(old($Heap), root#0, n#7, S#0) } 
        { read($Heap, n#7, M2.Node.marked) } 
        { S#0[$Box(n#7)] } 
      $Is(n#7, Tclass.M2.Node())
         ==> 
        S#0[$Box(n#7)] && read($Heap, n#7, M2.Node.marked)
         ==> M2.__default.Reachable(old($Heap), root#0, n#7, S#0));
  free ensures true;
  ensures $_reverifyPost
     ==> (forall n#9: ref :: 
      { read(old($Heap), n#9, M2.Node.children) } 
        { read($Heap, n#9, M2.Node.children) } 
        { read(old($Heap), n#9, M2.Node.childrenVisited) } 
        { read($Heap, n#9, M2.Node.childrenVisited) } 
        { S#0[$Box(n#9)] } 
      $Is(n#9, Tclass.M2.Node())
         ==> (S#0[$Box(n#9)]
             ==> read($Heap, n#9, M2.Node.childrenVisited)
               == read(old($Heap), n#9, M2.Node.childrenVisited))
           && (S#0[$Box(n#9)]
             ==> Seq#Equal(read($Heap, n#9, M2.Node.children), read(old($Heap), n#9, M2.Node.children))));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || S#0[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$M2.__default.SchorrWaite(root#0: ref, S#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var path#0: DatatypeType
     where $Is(path#0, Tclass.M2.Path()) && $IsAlloc(path#0, Tclass.M2.Path(), $Heap);
  var $rhs#0: DatatypeType where $Is($rhs#0, Tclass.M2.Path());
  var $rhs#1: bool;
  var t#0: ref
     where $Is(t#0, Tclass.M2.Node()) && $IsAlloc(t#0, Tclass.M2.Node(), $Heap);
  var p#0: ref
     where $Is(p#0, Tclass.M2.Node?()) && $IsAlloc(p#0, Tclass.M2.Node?(), $Heap);
  var $rhs#2: ref where $Is($rhs#2, Tclass.M2.Node());
  var $rhs#3: ref where $Is($rhs#3, Tclass.M2.Node?());
  var stackNodes#0: Seq Box
     where $Is(stackNodes#0, TSeq(Tclass.M2.Node()))
       && $IsAlloc(stackNodes#0, TSeq(Tclass.M2.Node()), $Heap);
  var $Heap_at_0: Heap;
  var $PreLoopHeap$loop#0: Heap;
  var $w$loop#0: bool;
  var i#0: int;
  var n#10: ref;
  var n#12: ref;
  var n#14: ref;
  var j#0: int;
  var n#16: ref;
  var k#0: int;
  var k#2: int;
  var n#18: ref;
  var ch#6: ref;
  var n#20: ref;
  var j#2: int;
  var ##source#1: ref;
  var ##p#0: DatatypeType;
  var ##sink#1: ref;
  var ##S#1: Set Box;
  var n#22: ref;
  var pth#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##source#2: ref;
  var ##p#1: DatatypeType;
  var ##sink#2: ref;
  var ##S#2: Set Box;
  var n#24: ref;
  var ##source#3: ref;
  var ##sink#3: ref;
  var ##S#3: Set Box;
  var $rhs#0_0_0: int where LitInt(0) <= $rhs#0_0_0;
  var $obj2: ref;
  var $rhs#0_0_1: ref where $Is($rhs#0_0_1, Tclass.M2.Node());
  var $rhs#0_0_2: ref where $Is($rhs#0_0_2, Tclass.M2.Node?());
  var $rhs#0_0_3: Seq Box where $Is($rhs#0_0_3, TSeq(Tclass.M2.Node?()));
  var $rhs#0_0_4: int where LitInt(0) <= $rhs#0_0_4;
  var $rhs#0_1_0: int where LitInt(0) <= $rhs#0_1_0;
  var $rhs#0_0: ref where $Is($rhs#0_0, Tclass.M2.Node());
  var $rhs#0_1: ref where $Is($rhs#0_1, Tclass.M2.Node?());
  var $rhs#0_2: Seq Box where $Is($rhs#0_2, TSeq(Tclass.M2.Node?()));
  var $rhs#0_3: bool;
  var $rhs#0_4: DatatypeType where $Is($rhs#0_4, Tclass.M2.Path());
  var n#26: ref;
  var ch#8: ref;
  var n#28: ref;
  var ##source#4: ref;
  var ##sink#4: ref;
  var ##S#4: Set Box;

    // AddMethodImpl: SchorrWaite, Impl$$M2.__default.SchorrWaite
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> S#0[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(199,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(200,20)
    assume true;
    assume true;
    path#0 := Lit(#M2.Path.Empty());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(200,32)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(201,23)
    assert root#0 != null;
    assume true;
    assert $_Frame[root#0, M2.Node.pathFromRoot];
    assume true;
    $rhs#0 := path#0;
    $Heap := update($Heap, root#0, M2.Node.pathFromRoot, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(201,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](57,17)
    assume root#0 != null;
    assume true;
    assume $_Frame[root#0, M2.Node.marked];
    assume true;
    $rhs#1 := Lit(true);
    $Heap := update($Heap, root#0, M2.Node.marked, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](57,23)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](58,21)
    assume true;
    assume true;
    assume true;
    $rhs#2 := root#0;
    assume true;
    $rhs#3 := null;
    t#0 := $rhs#2;
    p#0 := $rhs#3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](58,33)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](59,37)
    assume true;
    assume true;
    stackNodes#0 := Lit(Seq#Empty(): Seq Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](59,41)"} true;
    $Heap_at_0 := $Heap;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(203,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall i#1: int :: 
          { $Unbox(Seq#Index(stackNodes#0, i#1)): ref } 
          true
             ==> 
            LitInt(0) <= i#1 && i#1 < Seq#Length(stackNodes#0)
             ==> S#0[Seq#Index(stackNodes#0, i#1)]);
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0 ==> S#0[$Box(t#0)];
      free invariant $w$loop#0 ==> !Seq#Contains(stackNodes#0, $Box(t#0));
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> p#0
           == (if Seq#Length(stackNodes#0) == LitInt(0)
             then null
             else $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref);
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall n#11: ref :: 
          { read($Heap, n#11, M2.Node.children) } 
            { read($Heap, n#11, M2.Node.childrenVisited) } 
            { Seq#Contains(stackNodes#0, $Box(n#11)) } 
          $Is(n#11, Tclass.M2.Node())
             ==> 
            Seq#Contains(stackNodes#0, $Box(n#11))
             ==> read($Heap, n#11, M2.Node.childrenVisited)
               < Seq#Length(read($Heap, n#11, M2.Node.children)));
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> read($Heap, t#0, M2.Node.childrenVisited)
           <= Seq#Length(read($Heap, t#0, M2.Node.children));
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall n#13: ref :: 
          { read($Heap, n#13, M2.Node.childrenVisited) } 
            { Seq#Contains(stackNodes#0, $Box(n#13)) } 
            { S#0[$Box(n#13)] } 
          $Is(n#13, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#13)] && !Seq#Contains(stackNodes#0, $Box(n#13)) && n#13 != t#0
             ==> read($Heap, n#13, M2.Node.childrenVisited) == LitInt(0));
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall n#15: ref :: 
          { read($Heap, n#15, M2.Node.childrenVisited) } 
            { read(old($Heap), n#15, M2.Node.children) } 
            { read($Heap, n#15, M2.Node.children) } 
            { Seq#Contains(stackNodes#0, $Box(n#15)) } 
          $Is(n#15, Tclass.M2.Node())
             ==> (Seq#Contains(stackNodes#0, $Box(n#15))
                 ==> Seq#Length(read($Heap, n#15, M2.Node.children))
                   == Seq#Length(read(old($Heap), n#15, M2.Node.children)))
               && (Seq#Contains(stackNodes#0, $Box(n#15))
                 ==> (forall j#1: int :: 
                  { $Unbox(Seq#Index(read(old($Heap), n#15, M2.Node.children), j#1)): ref } 
                    { $Unbox(Seq#Index(read($Heap, n#15, M2.Node.children), j#1)): ref } 
                  true
                     ==> 
                    LitInt(0) <= j#1 && j#1 < Seq#Length(read($Heap, n#15, M2.Node.children))
                     ==> j#1 == read($Heap, n#15, M2.Node.childrenVisited)
                       || $Unbox(Seq#Index(read($Heap, n#15, M2.Node.children), j#1)): ref
                         == $Unbox(Seq#Index(read(old($Heap), n#15, M2.Node.children), j#1)): ref)));
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall n#17: ref :: 
          { read(old($Heap), n#17, M2.Node.children) } 
            { read($Heap, n#17, M2.Node.children) } 
            { Seq#Contains(stackNodes#0, $Box(n#17)) } 
            { S#0[$Box(n#17)] } 
          $Is(n#17, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#17)] && !Seq#Contains(stackNodes#0, $Box(n#17))
             ==> Seq#Equal(read($Heap, n#17, M2.Node.children), read(old($Heap), n#17, M2.Node.children)));
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> 
        0 < Seq#Length(stackNodes#0)
         ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, M2.Node.children), 
              read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, M2.Node.childrenVisited))): ref
           == null;
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall k#1: int :: 
          {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, M2.Node.childrenVisited) } 
            { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, M2.Node.children) } 
          true
             ==> 
            0 < k#1 && k#1 < Seq#Length(stackNodes#0)
             ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, M2.Node.children), 
                  read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, M2.Node.childrenVisited))): ref
               == $Unbox(Seq#Index(stackNodes#0, k#1 - 1)): ref);
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall k#3: int :: 
          {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, M2.Node.childrenVisited) } 
            { $Unbox(Seq#Index(stackNodes#0, k#3)): ref } 
          true
             ==> 
            LitInt(0) <= k#3 && k#3 < Seq#Length(stackNodes#0) - 1
             ==> $Unbox(Seq#Index(read(old($Heap), $Unbox(Seq#Index(stackNodes#0, k#3)): ref, M2.Node.children), 
                  read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, M2.Node.childrenVisited))): ref
               == $Unbox(Seq#Index(stackNodes#0, k#3 + 1)): ref);
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> 
        0 < Seq#Length(stackNodes#0)
         ==> $Unbox(Seq#Index(read(old($Heap), 
                $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref, 
                M2.Node.children), 
              read($Heap, 
                $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref, 
                M2.Node.childrenVisited))): ref
           == t#0;
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0 ==> read($Heap, root#0, M2.Node.marked);
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall n#19: ref :: 
          { read($Heap, n#19, M2.Node.children) } 
            { Seq#Contains(stackNodes#0, $Box(n#19)) } 
            { read($Heap, n#19, M2.Node.marked) } 
            { S#0[$Box(n#19)] } 
          $Is(n#19, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#19)]
               && read($Heap, n#19, M2.Node.marked)
               && !Seq#Contains(stackNodes#0, $Box(n#19))
               && n#19 != t#0
             ==> (forall ch#7: ref :: 
              { read($Heap, ch#7, M2.Node.marked) } 
                { Seq#Contains(read($Heap, n#19, M2.Node.children), $Box(ch#7)) } 
              $Is(ch#7, Tclass.M2.Node?())
                 ==> 
                Seq#Contains(read($Heap, n#19, M2.Node.children), $Box(ch#7)) && ch#7 != null
                 ==> read($Heap, ch#7, M2.Node.marked)));
      free invariant $w$loop#0 ==> true;
      free invariant $w$loop#0
         ==> (forall n#21: ref :: 
          { read($Heap, n#21, M2.Node.marked) } 
            { Seq#Contains(stackNodes#0, $Box(n#21)) } 
          $Is(n#21, Tclass.M2.Node())
             ==> 
            Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
             ==> read($Heap, n#21, M2.Node.marked));
      free invariant $w$loop#0
         ==> (forall n#21: ref :: 
          { read($Heap, n#21, M2.Node.children) } 
            { read($Heap, n#21, M2.Node.childrenVisited) } 
            { Seq#Contains(stackNodes#0, $Box(n#21)) } 
          $Is(n#21, Tclass.M2.Node())
             ==> 
            Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
             ==> (forall j#3: int :: 
              { $Unbox(Seq#Index(read($Heap, n#21, M2.Node.children), j#3)): ref } 
              true
                 ==> 
                LitInt(0) <= j#3 && j#3 < read($Heap, n#21, M2.Node.childrenVisited)
                 ==> $Unbox(Seq#Index(read($Heap, n#21, M2.Node.children), j#3)): ref == null
                   || read($Heap, 
                    $Unbox(Seq#Index(read($Heap, n#21, M2.Node.children), j#3)): ref, 
                    M2.Node.marked)));
      free invariant $w$loop#0
         ==> 
        $IsAlloc(path#0, Tclass.M2.Path(), old($Heap))
         ==> M2.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0);
      invariant $w$loop#0 ==> $IsAlloc(path#0, Tclass.M2.Path(), old($Heap));
      invariant $w$loop#0
         ==> M2.__default.ReachableVia($LS($LS($LZ)), old($Heap), root#0, path#0, t#0, S#0);
      free invariant $w$loop#0
         ==> (forall n#23: ref :: 
          { M2.__default.ReachableVia($LS($LZ), 
              old($Heap), 
              root#0, 
              read(old($Heap), n#23, M2.Node.pathFromRoot), 
              n#23, 
              S#0) } 
            { read($Heap, n#23, M2.Node.pathFromRoot) } 
            { read($Heap, n#23, M2.Node.marked) } 
            { S#0[$Box(n#23)] } 
          $Is(n#23, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#23)]
             ==> 
            read($Heap, n#23, M2.Node.marked)
             ==> (var pth#0 := read($Heap, n#23, M2.Node.pathFromRoot); 
              $IsAlloc(pth#0, Tclass.M2.Path(), old($Heap))
                 ==> M2.__default.ReachableVia#canCall(old($Heap), root#0, pth#0, n#23, S#0)));
      invariant $w$loop#0
         ==> (forall n#23: ref :: 
          { M2.__default.ReachableVia($LS($LZ), 
              old($Heap), 
              root#0, 
              read(old($Heap), n#23, M2.Node.pathFromRoot), 
              n#23, 
              S#0) } 
            { read($Heap, n#23, M2.Node.pathFromRoot) } 
            { read($Heap, n#23, M2.Node.marked) } 
            { S#0[$Box(n#23)] } 
          $Is(n#23, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#23)] && read($Heap, n#23, M2.Node.marked)
             ==> (var pth#0 := read($Heap, n#23, M2.Node.pathFromRoot); 
              $IsAlloc(pth#0, Tclass.M2.Path(), old($Heap))
                 && M2.__default.ReachableVia($LS($LZ), old($Heap), root#0, pth#0, n#23, S#0)));
      free invariant $w$loop#0
         ==> (forall n#25: ref :: 
          { M2.__default.Reachable(old($Heap), root#0, n#25, S#0) } 
            { read($Heap, n#25, M2.Node.marked) } 
            { S#0[$Box(n#25)] } 
          $Is(n#25, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#25)]
             ==> 
            read($Heap, n#25, M2.Node.marked)
             ==> M2.__default.Reachable#canCall(old($Heap), root#0, n#25, S#0));
      invariant $w$loop#0
         ==> (forall n#25: ref :: 
          { M2.__default.Reachable(old($Heap), root#0, n#25, S#0) } 
            { read($Heap, n#25, M2.Node.marked) } 
            { S#0[$Box(n#25)] } 
          $Is(n#25, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#25)] && read($Heap, n#25, M2.Node.marked)
             ==> M2.__default.Reachable(old($Heap), root#0, n#25, S#0));
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o] || S#0[$Box($o)]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(203,4): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            // Begin Comprehension WF check
            havoc i#0;
            if (true)
            {
                if (LitInt(0) <= i#0)
                {
                }

                if (LitInt(0) <= i#0 && i#0 < Seq#Length(stackNodes#0))
                {
                    assume {:subsumption 0} 0 <= i#0 && i#0 < Seq#Length(stackNodes#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall i#1: int :: 
              { $Unbox(Seq#Index(stackNodes#0, i#1)): ref } 
              true
                 ==> 
                LitInt(0) <= i#1 && i#1 < Seq#Length(stackNodes#0)
                 ==> S#0[Seq#Index(stackNodes#0, i#1)]);
            if (S#0[$Box(t#0)])
            {
            }

            assume true;
            assume S#0[$Box(t#0)] && !Seq#Contains(stackNodes#0, $Box(t#0));
            if (Seq#Length(stackNodes#0) == LitInt(0))
            {
            }
            else
            {
                assume {:subsumption 0} 0 <= Seq#Length(stackNodes#0) - 1
                   && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
            }

            assume true;
            assume p#0
               == (if Seq#Length(stackNodes#0) == LitInt(0)
                 then null
                 else $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref);
            // Begin Comprehension WF check
            havoc n#10;
            if ($Is(n#10, Tclass.M2.Node()))
            {
                if (Seq#Contains(stackNodes#0, $Box(n#10)))
                {
                    assume {:subsumption 0} n#10 != null;
                    assume {:subsumption 0} n#10 != null;
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#11: ref :: 
              { read($Heap, n#11, M2.Node.children) } 
                { read($Heap, n#11, M2.Node.childrenVisited) } 
                { Seq#Contains(stackNodes#0, $Box(n#11)) } 
              $Is(n#11, Tclass.M2.Node())
                 ==> 
                Seq#Contains(stackNodes#0, $Box(n#11))
                 ==> read($Heap, n#11, M2.Node.childrenVisited)
                   < Seq#Length(read($Heap, n#11, M2.Node.children)));
            assume {:subsumption 0} t#0 != null;
            assume {:subsumption 0} t#0 != null;
            assume true;
            assume read($Heap, t#0, M2.Node.childrenVisited)
               <= Seq#Length(read($Heap, t#0, M2.Node.children));
            // Begin Comprehension WF check
            havoc n#12;
            if ($Is(n#12, Tclass.M2.Node()))
            {
                if (S#0[$Box(n#12)])
                {
                }

                if (S#0[$Box(n#12)] && !Seq#Contains(stackNodes#0, $Box(n#12)))
                {
                }

                if (S#0[$Box(n#12)] && !Seq#Contains(stackNodes#0, $Box(n#12)) && n#12 != t#0)
                {
                    assume {:subsumption 0} n#12 != null;
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#13: ref :: 
              { read($Heap, n#13, M2.Node.childrenVisited) } 
                { Seq#Contains(stackNodes#0, $Box(n#13)) } 
                { S#0[$Box(n#13)] } 
              $Is(n#13, Tclass.M2.Node())
                 ==> 
                S#0[$Box(n#13)] && !Seq#Contains(stackNodes#0, $Box(n#13)) && n#13 != t#0
                 ==> read($Heap, n#13, M2.Node.childrenVisited) == LitInt(0));
            // Begin Comprehension WF check
            havoc n#14;
            if ($Is(n#14, Tclass.M2.Node()))
            {
                if (Seq#Contains(stackNodes#0, $Box(n#14)))
                {
                    assume {:subsumption 0} n#14 != null;
                    assume {:subsumption 0} n#14 != null;
                    assume $IsAlloc(n#14, Tclass.M2.Node(), old($Heap));
                    if (Seq#Length(read($Heap, n#14, M2.Node.children))
                       == Seq#Length(read(old($Heap), n#14, M2.Node.children)))
                    {
                        // Begin Comprehension WF check
                        havoc j#0;
                        if (true)
                        {
                            if (LitInt(0) <= j#0)
                            {
                                assume {:subsumption 0} n#14 != null;
                            }

                            if (LitInt(0) <= j#0 && j#0 < Seq#Length(read($Heap, n#14, M2.Node.children)))
                            {
                                assume {:subsumption 0} n#14 != null;
                                if (j#0 != read($Heap, n#14, M2.Node.childrenVisited))
                                {
                                    assume {:subsumption 0} n#14 != null;
                                    assume {:subsumption 0} 0 <= j#0 && j#0 < Seq#Length(read($Heap, n#14, M2.Node.children));
                                    assume {:subsumption 0} n#14 != null;
                                    assume $IsAlloc(n#14, Tclass.M2.Node(), old($Heap));
                                    assume {:subsumption 0} 0 <= j#0 && j#0 < Seq#Length(read(old($Heap), n#14, M2.Node.children));
                                }
                            }
                        }

                        // End Comprehension WF check
                    }
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#15: ref :: 
              { read($Heap, n#15, M2.Node.childrenVisited) } 
                { read(old($Heap), n#15, M2.Node.children) } 
                { read($Heap, n#15, M2.Node.children) } 
                { Seq#Contains(stackNodes#0, $Box(n#15)) } 
              $Is(n#15, Tclass.M2.Node())
                 ==> (Seq#Contains(stackNodes#0, $Box(n#15))
                     ==> Seq#Length(read($Heap, n#15, M2.Node.children))
                       == Seq#Length(read(old($Heap), n#15, M2.Node.children)))
                   && (Seq#Contains(stackNodes#0, $Box(n#15))
                     ==> (forall j#1: int :: 
                      { $Unbox(Seq#Index(read(old($Heap), n#15, M2.Node.children), j#1)): ref } 
                        { $Unbox(Seq#Index(read($Heap, n#15, M2.Node.children), j#1)): ref } 
                      true
                         ==> 
                        LitInt(0) <= j#1 && j#1 < Seq#Length(read($Heap, n#15, M2.Node.children))
                         ==> j#1 == read($Heap, n#15, M2.Node.childrenVisited)
                           || $Unbox(Seq#Index(read($Heap, n#15, M2.Node.children), j#1)): ref
                             == $Unbox(Seq#Index(read(old($Heap), n#15, M2.Node.children), j#1)): ref)));
            // Begin Comprehension WF check
            havoc n#16;
            if ($Is(n#16, Tclass.M2.Node()))
            {
                if (S#0[$Box(n#16)])
                {
                }

                if (S#0[$Box(n#16)] && !Seq#Contains(stackNodes#0, $Box(n#16)))
                {
                    assume {:subsumption 0} n#16 != null;
                    assume {:subsumption 0} n#16 != null;
                    assume $IsAlloc(n#16, Tclass.M2.Node(), old($Heap));
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#17: ref :: 
              { read(old($Heap), n#17, M2.Node.children) } 
                { read($Heap, n#17, M2.Node.children) } 
                { Seq#Contains(stackNodes#0, $Box(n#17)) } 
                { S#0[$Box(n#17)] } 
              $Is(n#17, Tclass.M2.Node())
                 ==> 
                S#0[$Box(n#17)] && !Seq#Contains(stackNodes#0, $Box(n#17))
                 ==> Seq#Equal(read($Heap, n#17, M2.Node.children), read(old($Heap), n#17, M2.Node.children)));
            if (0 < Seq#Length(stackNodes#0))
            {
                assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(stackNodes#0);
                assume {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref != null;
                assume {:subsumption 0} 0 <= LitInt(0) && LitInt(0) < Seq#Length(stackNodes#0);
                assume {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref != null;
                assume {:subsumption 0} 0
                     <= read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, M2.Node.childrenVisited)
                   && read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, M2.Node.childrenVisited)
                     < Seq#Length(read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, M2.Node.children));
            }

            assume true;
            assume 0 < Seq#Length(stackNodes#0)
               ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, M2.Node.children), 
                    read($Heap, $Unbox(Seq#Index(stackNodes#0, LitInt(0))): ref, M2.Node.childrenVisited))): ref
                 == null;
            // Begin Comprehension WF check
            havoc k#0;
            if (true)
            {
                if (0 < k#0)
                {
                }

                if (0 < k#0 && k#0 < Seq#Length(stackNodes#0))
                {
                    assume {:subsumption 0} 0 <= k#0 && k#0 < Seq#Length(stackNodes#0);
                    assume {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, k#0)): ref != null;
                    assume {:subsumption 0} 0 <= k#0 && k#0 < Seq#Length(stackNodes#0);
                    assume {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, k#0)): ref != null;
                    assume {:subsumption 0} 0
                         <= read($Heap, $Unbox(Seq#Index(stackNodes#0, k#0)): ref, M2.Node.childrenVisited)
                       && read($Heap, $Unbox(Seq#Index(stackNodes#0, k#0)): ref, M2.Node.childrenVisited)
                         < Seq#Length(read($Heap, $Unbox(Seq#Index(stackNodes#0, k#0)): ref, M2.Node.children));
                    assume {:subsumption 0} 0 <= k#0 - 1 && k#0 - 1 < Seq#Length(stackNodes#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall k#1: int :: 
              {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, M2.Node.childrenVisited) } 
                { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, M2.Node.children) } 
              true
                 ==> 
                0 < k#1 && k#1 < Seq#Length(stackNodes#0)
                 ==> $Unbox(Seq#Index(read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, M2.Node.children), 
                      read($Heap, $Unbox(Seq#Index(stackNodes#0, k#1)): ref, M2.Node.childrenVisited))): ref
                   == $Unbox(Seq#Index(stackNodes#0, k#1 - 1)): ref);
            // Begin Comprehension WF check
            havoc k#2;
            if (true)
            {
                if (LitInt(0) <= k#2)
                {
                }

                if (LitInt(0) <= k#2 && k#2 < Seq#Length(stackNodes#0) - 1)
                {
                    assume {:subsumption 0} 0 <= k#2 && k#2 < Seq#Length(stackNodes#0);
                    assume {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, k#2)): ref != null;
                    assume $IsAlloc($Unbox(Seq#Index(stackNodes#0, k#2)): ref, Tclass.M2.Node(), old($Heap));
                    assume {:subsumption 0} 0 <= k#2 && k#2 < Seq#Length(stackNodes#0);
                    assume {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, k#2)): ref != null;
                    assume {:subsumption 0} 0
                         <= read($Heap, $Unbox(Seq#Index(stackNodes#0, k#2)): ref, M2.Node.childrenVisited)
                       && read($Heap, $Unbox(Seq#Index(stackNodes#0, k#2)): ref, M2.Node.childrenVisited)
                         < Seq#Length(read(old($Heap), $Unbox(Seq#Index(stackNodes#0, k#2)): ref, M2.Node.children));
                    assume {:subsumption 0} 0 <= k#2 + 1 && k#2 + 1 < Seq#Length(stackNodes#0);
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall k#3: int :: 
              {:matchinglooprewrite false} { read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, M2.Node.childrenVisited) } 
                { $Unbox(Seq#Index(stackNodes#0, k#3)): ref } 
              true
                 ==> 
                LitInt(0) <= k#3 && k#3 < Seq#Length(stackNodes#0) - 1
                 ==> $Unbox(Seq#Index(read(old($Heap), $Unbox(Seq#Index(stackNodes#0, k#3)): ref, M2.Node.children), 
                      read($Heap, $Unbox(Seq#Index(stackNodes#0, k#3)): ref, M2.Node.childrenVisited))): ref
                   == $Unbox(Seq#Index(stackNodes#0, k#3 + 1)): ref);
            if (0 < Seq#Length(stackNodes#0))
            {
                assume {:subsumption 0} 0 <= Seq#Length(stackNodes#0) - 1
                   && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
                assume {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref != null;
                assume $IsAlloc($Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref, 
                  Tclass.M2.Node(), 
                  old($Heap));
                assume {:subsumption 0} 0 <= Seq#Length(stackNodes#0) - 1
                   && Seq#Length(stackNodes#0) - 1 < Seq#Length(stackNodes#0);
                assume {:subsumption 0} $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref != null;
                assume {:subsumption 0} 0
                     <= read($Heap, 
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref, 
                      M2.Node.childrenVisited)
                   && read($Heap, 
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref, 
                      M2.Node.childrenVisited)
                     < Seq#Length(read(old($Heap), 
                        $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref, 
                        M2.Node.children));
            }

            assume true;
            assume 0 < Seq#Length(stackNodes#0)
               ==> $Unbox(Seq#Index(read(old($Heap), 
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref, 
                      M2.Node.children), 
                    read($Heap, 
                      $Unbox(Seq#Index(stackNodes#0, Seq#Length(stackNodes#0) - 1)): ref, 
                      M2.Node.childrenVisited))): ref
                 == t#0;
            assume {:subsumption 0} root#0 != null;
            assume true;
            assume read($Heap, root#0, M2.Node.marked);
            // Begin Comprehension WF check
            havoc n#18;
            if ($Is(n#18, Tclass.M2.Node()))
            {
                if (S#0[$Box(n#18)])
                {
                    assume {:subsumption 0} n#18 != null;
                }

                if (S#0[$Box(n#18)] && read($Heap, n#18, M2.Node.marked))
                {
                }

                if (S#0[$Box(n#18)]
                   && read($Heap, n#18, M2.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#18)))
                {
                }

                if (S#0[$Box(n#18)]
                   && read($Heap, n#18, M2.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#18))
                   && n#18 != t#0)
                {
                    // Begin Comprehension WF check
                    havoc ch#6;
                    if ($Is(ch#6, Tclass.M2.Node?()))
                    {
                        assume {:subsumption 0} n#18 != null;
                        if (Seq#Contains(read($Heap, n#18, M2.Node.children), $Box(ch#6)))
                        {
                        }

                        if (Seq#Contains(read($Heap, n#18, M2.Node.children), $Box(ch#6)) && ch#6 != null)
                        {
                            assume {:subsumption 0} ch#6 != null;
                        }
                    }

                    // End Comprehension WF check
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#19: ref :: 
              { read($Heap, n#19, M2.Node.children) } 
                { Seq#Contains(stackNodes#0, $Box(n#19)) } 
                { read($Heap, n#19, M2.Node.marked) } 
                { S#0[$Box(n#19)] } 
              $Is(n#19, Tclass.M2.Node())
                 ==> 
                S#0[$Box(n#19)]
                   && read($Heap, n#19, M2.Node.marked)
                   && !Seq#Contains(stackNodes#0, $Box(n#19))
                   && n#19 != t#0
                 ==> (forall ch#7: ref :: 
                  { read($Heap, ch#7, M2.Node.marked) } 
                    { Seq#Contains(read($Heap, n#19, M2.Node.children), $Box(ch#7)) } 
                  $Is(ch#7, Tclass.M2.Node?())
                     ==> 
                    Seq#Contains(read($Heap, n#19, M2.Node.children), $Box(ch#7)) && ch#7 != null
                     ==> read($Heap, ch#7, M2.Node.marked)));
            // Begin Comprehension WF check
            havoc n#20;
            if ($Is(n#20, Tclass.M2.Node()))
            {
                if (!Seq#Contains(stackNodes#0, $Box(n#20)))
                {
                }

                if (Seq#Contains(stackNodes#0, $Box(n#20)) || n#20 == t#0)
                {
                    assume {:subsumption 0} n#20 != null;
                    if (read($Heap, n#20, M2.Node.marked))
                    {
                        // Begin Comprehension WF check
                        havoc j#2;
                        if (true)
                        {
                            if (LitInt(0) <= j#2)
                            {
                                assume {:subsumption 0} n#20 != null;
                            }

                            if (LitInt(0) <= j#2 && j#2 < read($Heap, n#20, M2.Node.childrenVisited))
                            {
                                assume {:subsumption 0} n#20 != null;
                                assume {:subsumption 0} 0 <= j#2 && j#2 < Seq#Length(read($Heap, n#20, M2.Node.children));
                                if ($Unbox(Seq#Index(read($Heap, n#20, M2.Node.children), j#2)): ref != null)
                                {
                                    assume {:subsumption 0} n#20 != null;
                                    assume {:subsumption 0} 0 <= j#2 && j#2 < Seq#Length(read($Heap, n#20, M2.Node.children));
                                    assume {:subsumption 0} $Unbox(Seq#Index(read($Heap, n#20, M2.Node.children), j#2)): ref != null;
                                }
                            }
                        }

                        // End Comprehension WF check
                    }
                }
            }

            // End Comprehension WF check
            assume true;
            assume (forall n#21: ref :: 
                { read($Heap, n#21, M2.Node.marked) } 
                  { Seq#Contains(stackNodes#0, $Box(n#21)) } 
                $Is(n#21, Tclass.M2.Node())
                   ==> 
                  Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
                   ==> read($Heap, n#21, M2.Node.marked))
               && (forall n#21: ref :: 
                { read($Heap, n#21, M2.Node.children) } 
                  { read($Heap, n#21, M2.Node.childrenVisited) } 
                  { Seq#Contains(stackNodes#0, $Box(n#21)) } 
                $Is(n#21, Tclass.M2.Node())
                   ==> 
                  Seq#Contains(stackNodes#0, $Box(n#21)) || n#21 == t#0
                   ==> (forall j#3: int :: 
                    { $Unbox(Seq#Index(read($Heap, n#21, M2.Node.children), j#3)): ref } 
                    true
                       ==> 
                      LitInt(0) <= j#3 && j#3 < read($Heap, n#21, M2.Node.childrenVisited)
                       ==> $Unbox(Seq#Index(read($Heap, n#21, M2.Node.children), j#3)): ref == null
                         || read($Heap, 
                          $Unbox(Seq#Index(read($Heap, n#21, M2.Node.children), j#3)): ref, 
                          M2.Node.marked)));
            if ($IsAlloc(path#0, Tclass.M2.Path(), old($Heap)))
            {
                ##source#1 := root#0;
                ##p#0 := path#0;
                ##sink#1 := t#0;
                ##S#1 := S#0;
                assert $IsAlloc(root#0, Tclass.M2.Node(), old($Heap));
                assert $IsAlloc(path#0, Tclass.M2.Path(), old($Heap));
                assert $IsAlloc(t#0, Tclass.M2.Node(), old($Heap));
                assert $IsAlloc(S#0, TSet(Tclass.M2.Node()), old($Heap));
                assume M2.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0);
            }

            assume $IsAlloc(path#0, Tclass.M2.Path(), old($Heap))
               ==> M2.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0);
            assume $IsAlloc(path#0, Tclass.M2.Path(), old($Heap))
               && M2.__default.ReachableVia($LS($LZ), old($Heap), root#0, path#0, t#0, S#0);
            // Begin Comprehension WF check
            havoc n#22;
            if ($Is(n#22, Tclass.M2.Node()))
            {
                if (S#0[$Box(n#22)])
                {
                    assert {:subsumption 0} n#22 != null;
                }

                if (S#0[$Box(n#22)] && read($Heap, n#22, M2.Node.marked))
                {
                    havoc pth#Z#0;
                    assume $Is(pth#Z#0, Tclass.M2.Path());
                    assert {:subsumption 0} n#22 != null;
                    assume let#0#0#0 == read($Heap, n#22, M2.Node.pathFromRoot);
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(let#0#0#0, Tclass.M2.Path());
                    assume pth#Z#0 == let#0#0#0;
                    if ($IsAlloc(pth#Z#0, Tclass.M2.Path(), old($Heap)))
                    {
                        ##source#2 := root#0;
                        ##p#1 := pth#Z#0;
                        ##sink#2 := n#22;
                        ##S#2 := S#0;
                        assert $IsAlloc(root#0, Tclass.M2.Node(), old($Heap));
                        assert $IsAlloc(pth#Z#0, Tclass.M2.Path(), old($Heap));
                        assert $IsAlloc(n#22, Tclass.M2.Node(), old($Heap));
                        assert $IsAlloc(S#0, TSet(Tclass.M2.Node()), old($Heap));
                        assume M2.__default.ReachableVia#canCall(old($Heap), root#0, pth#Z#0, n#22, S#0);
                    }
                }
            }

            // End Comprehension WF check
            assume (forall n#23: ref :: 
              { M2.__default.ReachableVia($LS($LZ), 
                  old($Heap), 
                  root#0, 
                  read(old($Heap), n#23, M2.Node.pathFromRoot), 
                  n#23, 
                  S#0) } 
                { read($Heap, n#23, M2.Node.pathFromRoot) } 
                { read($Heap, n#23, M2.Node.marked) } 
                { S#0[$Box(n#23)] } 
              $Is(n#23, Tclass.M2.Node())
                 ==> 
                S#0[$Box(n#23)]
                 ==> 
                read($Heap, n#23, M2.Node.marked)
                 ==> (var pth#0 := read($Heap, n#23, M2.Node.pathFromRoot); 
                  $IsAlloc(pth#0, Tclass.M2.Path(), old($Heap))
                     ==> M2.__default.ReachableVia#canCall(old($Heap), root#0, pth#0, n#23, S#0)));
            assume (forall n#23: ref :: 
              { M2.__default.ReachableVia($LS($LZ), 
                  old($Heap), 
                  root#0, 
                  read(old($Heap), n#23, M2.Node.pathFromRoot), 
                  n#23, 
                  S#0) } 
                { read($Heap, n#23, M2.Node.pathFromRoot) } 
                { read($Heap, n#23, M2.Node.marked) } 
                { S#0[$Box(n#23)] } 
              $Is(n#23, Tclass.M2.Node())
                 ==> 
                S#0[$Box(n#23)] && read($Heap, n#23, M2.Node.marked)
                 ==> (var pth#0 := read($Heap, n#23, M2.Node.pathFromRoot); 
                  $IsAlloc(pth#0, Tclass.M2.Path(), old($Heap))
                     && M2.__default.ReachableVia($LS($LZ), old($Heap), root#0, pth#0, n#23, S#0)));
            // Begin Comprehension WF check
            havoc n#24;
            if ($Is(n#24, Tclass.M2.Node()))
            {
                if (S#0[$Box(n#24)])
                {
                    assert {:subsumption 0} n#24 != null;
                }

                if (S#0[$Box(n#24)] && read($Heap, n#24, M2.Node.marked))
                {
                    ##source#3 := root#0;
                    ##sink#3 := n#24;
                    ##S#3 := S#0;
                    assert $IsAlloc(root#0, Tclass.M2.Node(), old($Heap));
                    assert $IsAlloc(n#24, Tclass.M2.Node(), old($Heap));
                    assert $IsAlloc(S#0, TSet(Tclass.M2.Node()), old($Heap));
                    assume M2.__default.Reachable#canCall(old($Heap), root#0, n#24, S#0);
                }
            }

            // End Comprehension WF check
            assume (forall n#25: ref :: 
              { M2.__default.Reachable(old($Heap), root#0, n#25, S#0) } 
                { read($Heap, n#25, M2.Node.marked) } 
                { S#0[$Box(n#25)] } 
              $Is(n#25, Tclass.M2.Node())
                 ==> 
                S#0[$Box(n#25)]
                 ==> 
                read($Heap, n#25, M2.Node.marked)
                 ==> M2.__default.Reachable#canCall(old($Heap), root#0, n#25, S#0));
            assume (forall n#25: ref :: 
              { M2.__default.Reachable(old($Heap), root#0, n#25, S#0) } 
                { read($Heap, n#25, M2.Node.marked) } 
                { S#0[$Box(n#25)] } 
              $Is(n#25, Tclass.M2.Node())
                 ==> 
                S#0[$Box(n#25)] && read($Heap, n#25, M2.Node.marked)
                 ==> M2.__default.Reachable(old($Heap), root#0, n#25, S#0));
            assume true;
            assume false;
        }

        assume true;
        if (!Lit(true))
        {
            break;
        }

        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(222,7)
        assume t#0 != null;
        assume t#0 != null;
        assume true;
        if (read($Heap, t#0, M2.Node.childrenVisited)
           == Seq#Length(read($Heap, t#0, M2.Node.children)))
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](111,27)
            assume t#0 != null;
            assume true;
            assume $_Frame[t#0, M2.Node.childrenVisited];
            assume true;
            assume $Is(LitInt(0), Tclass._System.nat());
            $rhs#0_0_0 := LitInt(0);
            $Heap := update($Heap, t#0, M2.Node.childrenVisited, $rhs#0_0_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](111,30)"} true;
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](112,9)
            assume true;
            if (p#0 == null)
            {
                // ----- break statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](112,24)
                goto after_0;
            }
            else
            {
            }

            // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](114,26)
            assume true;
            assume true;
            assume p#0 != null;
            assume true;
            $obj2 := p#0;
            assume $_Frame[$obj2, M2.Node.children];
            assume true;
            assume $Is(p#0, Tclass.M2.Node());
            $rhs#0_0_1 := p#0;
            assume p#0 != null;
            assume p#0 != null;
            assume 0 <= read($Heap, p#0, M2.Node.childrenVisited)
               && read($Heap, p#0, M2.Node.childrenVisited)
                 < Seq#Length(read($Heap, p#0, M2.Node.children));
            assume true;
            $rhs#0_0_2 := $Unbox(Seq#Index(read($Heap, p#0, M2.Node.children), read($Heap, p#0, M2.Node.childrenVisited))): ref;
            assume p#0 != null;
            assume p#0 != null;
            assume 0 <= read($Heap, p#0, M2.Node.childrenVisited)
               && read($Heap, p#0, M2.Node.childrenVisited)
                 < Seq#Length(read($Heap, p#0, M2.Node.children));
            assume true;
            $rhs#0_0_3 := Seq#Update(read($Heap, p#0, M2.Node.children), 
              read($Heap, p#0, M2.Node.childrenVisited), 
              $Box(t#0));
            t#0 := $rhs#0_0_1;
            p#0 := $rhs#0_0_2;
            $Heap := update($Heap, $obj2, M2.Node.children, $rhs#0_0_3);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](114,96)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](115,20)
            assume true;
            assume 0 <= Seq#Length(stackNodes#0) - 1
               && Seq#Length(stackNodes#0) - 1 <= Seq#Length(stackNodes#0);
            assume true;
            stackNodes#0 := Seq#Take(stackNodes#0, Seq#Length(stackNodes#0) - 1);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](115,52)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](116,27)
            assume t#0 != null;
            assume true;
            assume $_Frame[t#0, M2.Node.childrenVisited];
            assume t#0 != null;
            assume true;
            assume $Is(read($Heap, t#0, M2.Node.childrenVisited) + 1, Tclass._System.nat());
            $rhs#0_0_4 := read($Heap, t#0, M2.Node.childrenVisited) + 1;
            $Heap := update($Heap, t#0, M2.Node.childrenVisited, $rhs#0_0_4);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](116,50)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(225,14)
            assume true;
            assert t#0 != null;
            assume true;
            path#0 := read($Heap, t#0, M2.Node.pathFromRoot);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(225,30)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(226,14)
            assume t#0 != null;
            assume t#0 != null;
            assume 0 <= read($Heap, t#0, M2.Node.childrenVisited)
               && read($Heap, t#0, M2.Node.childrenVisited)
                 < Seq#Length(read($Heap, t#0, M2.Node.children));
            if ($Unbox(Seq#Index(read($Heap, t#0, M2.Node.children), read($Heap, t#0, M2.Node.childrenVisited))): ref
               != null)
            {
                assume t#0 != null;
                assume t#0 != null;
                assume 0 <= read($Heap, t#0, M2.Node.childrenVisited)
                   && read($Heap, t#0, M2.Node.childrenVisited)
                     < Seq#Length(read($Heap, t#0, M2.Node.children));
                assume $Unbox(Seq#Index(read($Heap, t#0, M2.Node.children), read($Heap, t#0, M2.Node.childrenVisited))): ref
                   != null;
            }

            assume true;
            if ($Unbox(Seq#Index(read($Heap, t#0, M2.Node.children), read($Heap, t#0, M2.Node.childrenVisited))): ref
                 == null
               || read($Heap, 
                $Unbox(Seq#Index(read($Heap, t#0, M2.Node.children), read($Heap, t#0, M2.Node.childrenVisited))): ref, 
                M2.Node.marked))
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](120,27)
                assume t#0 != null;
                assume true;
                assume $_Frame[t#0, M2.Node.childrenVisited];
                assume t#0 != null;
                assume true;
                assume $Is(read($Heap, t#0, M2.Node.childrenVisited) + 1, Tclass._System.nat());
                $rhs#0_1_0 := read($Heap, t#0, M2.Node.childrenVisited) + 1;
                $Heap := update($Heap, t#0, M2.Node.childrenVisited, $rhs#0_1_0);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](120,50)"} true;
            }
            else
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(230,14)
                assume true;
                assume true;
                path#0 := #M2.Path.Extend(path#0, t#0);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(230,36)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](124,20)
                assume true;
                assume true;
                stackNodes#0 := Seq#Append(stackNodes#0, Seq#Build(Seq#Empty(): Seq Box, $Box(t#0)));
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](124,38)"} true;
                // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](125,26)
                assume true;
                assume true;
                assume t#0 != null;
                assume true;
                $obj2 := t#0;
                assume $_Frame[$obj2, M2.Node.children];
                assume t#0 != null;
                assume t#0 != null;
                assume 0 <= read($Heap, t#0, M2.Node.childrenVisited)
                   && read($Heap, t#0, M2.Node.childrenVisited)
                     < Seq#Length(read($Heap, t#0, M2.Node.children));
                assume true;
                assume $Is($Unbox(Seq#Index(read($Heap, t#0, M2.Node.children), read($Heap, t#0, M2.Node.childrenVisited))): ref, 
                  Tclass.M2.Node());
                $rhs#0_0 := $Unbox(Seq#Index(read($Heap, t#0, M2.Node.children), read($Heap, t#0, M2.Node.childrenVisited))): ref;
                assume true;
                $rhs#0_1 := t#0;
                assume t#0 != null;
                assume t#0 != null;
                assume 0 <= read($Heap, t#0, M2.Node.childrenVisited)
                   && read($Heap, t#0, M2.Node.childrenVisited)
                     < Seq#Length(read($Heap, t#0, M2.Node.children));
                assume true;
                $rhs#0_2 := Seq#Update(read($Heap, t#0, M2.Node.children), 
                  read($Heap, t#0, M2.Node.childrenVisited), 
                  $Box(p#0));
                t#0 := $rhs#0_0;
                p#0 := $rhs#0_1;
                $Heap := update($Heap, $obj2, M2.Node.children, $rhs#0_2);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](125,96)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](126,18)
                assume t#0 != null;
                assume true;
                assume $_Frame[t#0, M2.Node.marked];
                assume true;
                $rhs#0_3 := Lit(true);
                $Heap := update($Heap, t#0, M2.Node.marked, $rhs#0_3);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M1][M2](126,24)"} true;
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy[M2](169,9)
                assume true;
                assume !Seq#Contains(stackNodes#0, $Box(t#0));
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(232,24)
                assert t#0 != null;
                assume true;
                assert $_Frame[t#0, M2.Node.pathFromRoot];
                assume true;
                $rhs#0_4 := path#0;
                $Heap := update($Heap, t#0, M2.Node.pathFromRoot, $rhs#0_4);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(232,30)"} true;
            }
        }

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
        assume true;
        assume true;
        assume true;
        assume $IsAlloc(path#0, Tclass.M2.Path(), old($Heap))
           ==> M2.__default.ReachableVia#canCall(old($Heap), root#0, path#0, t#0, S#0);
        assume (forall n#23: ref :: 
          { M2.__default.ReachableVia($LS($LZ), 
              old($Heap), 
              root#0, 
              read(old($Heap), n#23, M2.Node.pathFromRoot), 
              n#23, 
              S#0) } 
            { read($Heap, n#23, M2.Node.pathFromRoot) } 
            { read($Heap, n#23, M2.Node.marked) } 
            { S#0[$Box(n#23)] } 
          $Is(n#23, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#23)]
             ==> 
            read($Heap, n#23, M2.Node.marked)
             ==> (var pth#0 := read($Heap, n#23, M2.Node.pathFromRoot); 
              $IsAlloc(pth#0, Tclass.M2.Path(), old($Heap))
                 ==> M2.__default.ReachableVia#canCall(old($Heap), root#0, pth#0, n#23, S#0)));
        assume (forall n#25: ref :: 
          { M2.__default.Reachable(old($Heap), root#0, n#25, S#0) } 
            { read($Heap, n#25, M2.Node.marked) } 
            { S#0[$Box(n#25)] } 
          $Is(n#25, Tclass.M2.Node())
             ==> 
            S#0[$Box(n#25)]
             ==> 
            read($Heap, n#25, M2.Node.marked)
             ==> M2.__default.Reachable#canCall(old($Heap), root#0, n#25, S#0));
    }

  after_0:
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(237,5)
    assume {:subsumption 0} root#0 != null;
    if (read($Heap, root#0, M2.Node.marked))
    {
        // Begin Comprehension WF check
        havoc n#26;
        if ($Is(n#26, Tclass.M2.Node()))
        {
            if (S#0[$Box(n#26)])
            {
                assume {:subsumption 0} n#26 != null;
            }

            if (S#0[$Box(n#26)] && read($Heap, n#26, M2.Node.marked))
            {
                // Begin Comprehension WF check
                havoc ch#8;
                if ($Is(ch#8, Tclass.M2.Node?()))
                {
                    assume {:subsumption 0} n#26 != null;
                    if (Seq#Contains(read($Heap, n#26, M2.Node.children), $Box(ch#8)))
                    {
                    }

                    if (Seq#Contains(read($Heap, n#26, M2.Node.children), $Box(ch#8)) && ch#8 != null)
                    {
                        assume {:subsumption 0} ch#8 != null;
                    }
                }

                // End Comprehension WF check
            }
        }

        // End Comprehension WF check
    }

    assume true;
    assert {:subsumption 0} {:_prependAssertToken} read($Heap, root#0, M2.Node.marked);
    assert {:subsumption 0} {:_prependAssertToken} (forall n#27: ref :: 
      { read($Heap, n#27, M2.Node.children) } 
        { read($Heap, n#27, M2.Node.marked) } 
        { S#0[$Box(n#27)] } 
      $Is(n#27, Tclass.M2.Node())
         ==> 
        S#0[$Box(n#27)] && read($Heap, n#27, M2.Node.marked)
         ==> (forall ch#9: ref :: 
          { read($Heap, ch#9, M2.Node.marked) } 
            { Seq#Contains(read($Heap, n#27, M2.Node.children), $Box(ch#9)) } 
          $Is(ch#9, Tclass.M2.Node?())
             ==> 
            Seq#Contains(read($Heap, n#27, M2.Node.children), $Box(ch#9)) && ch#9 != null
             ==> read($Heap, ch#9, M2.Node.marked)));
    assume read($Heap, root#0, M2.Node.marked)
       && (forall n#27: ref :: 
        { read($Heap, n#27, M2.Node.children) } 
          { read($Heap, n#27, M2.Node.marked) } 
          { S#0[$Box(n#27)] } 
        $Is(n#27, Tclass.M2.Node())
           ==> 
          S#0[$Box(n#27)] && read($Heap, n#27, M2.Node.marked)
           ==> (forall ch#9: ref :: 
            { read($Heap, ch#9, M2.Node.marked) } 
              { Seq#Contains(read($Heap, n#27, M2.Node.children), $Box(ch#9)) } 
            $Is(ch#9, Tclass.M2.Node?())
               ==> 
              Seq#Contains(read($Heap, n#27, M2.Node.children), $Box(ch#9)) && ch#9 != null
               ==> read($Heap, ch#9, M2.Node.marked)));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny1/SchorrWaite-stages.dfy(240,5)
    // Begin Comprehension WF check
    havoc n#28;
    if ($Is(n#28, Tclass.M2.Node()))
    {
        if (S#0[$Box(n#28)])
        {
            assume {:subsumption 0} n#28 != null;
        }

        if (S#0[$Box(n#28)] && read($Heap, n#28, M2.Node.marked))
        {
            ##source#4 := root#0;
            ##sink#4 := n#28;
            ##S#4 := S#0;
            assume $IsAlloc(root#0, Tclass.M2.Node(), old($Heap));
            assume $IsAlloc(n#28, Tclass.M2.Node(), old($Heap));
            assume $IsAlloc(S#0, TSet(Tclass.M2.Node()), old($Heap));
            assume M2.__default.Reachable#canCall(old($Heap), root#0, n#28, S#0);
        }
    }

    // End Comprehension WF check
    assume (forall n#29: ref :: 
      { M2.__default.Reachable(old($Heap), root#0, n#29, S#0) } 
        { read($Heap, n#29, M2.Node.marked) } 
        { S#0[$Box(n#29)] } 
      $Is(n#29, Tclass.M2.Node())
         ==> 
        S#0[$Box(n#29)]
         ==> 
        read($Heap, n#29, M2.Node.marked)
         ==> M2.__default.Reachable#canCall(old($Heap), root#0, n#29, S#0));
    assert {:_prependAssertToken} (forall n#29: ref :: 
      { M2.__default.Reachable(old($Heap), root#0, n#29, S#0) } 
        { read($Heap, n#29, M2.Node.marked) } 
        { S#0[$Box(n#29)] } 
      $Is(n#29, Tclass.M2.Node())
         ==> 
        S#0[$Box(n#29)] && read($Heap, n#29, M2.Node.marked)
         ==> M2.__default.Reachable(old($Heap), root#0, n#29, S#0));
}



// function declaration for M2._default.Reachable
function M2.__default.Reachable($heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box) : bool;

function M2.__default.Reachable#canCall($heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box) : bool;

// frame axiom for M2.__default.Reachable
axiom (forall $h0: Heap, $h1: Heap, source#0: ref, sink#0: ref, S#0: Set Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), M2.__default.Reachable($h1, source#0, sink#0, S#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (M2.__default.Reachable#canCall($h0, source#0, sink#0, S#0)
         || (
          $Is(source#0, Tclass.M2.Node())
           && $Is(sink#0, Tclass.M2.Node())
           && $Is(S#0, TSet(Tclass.M2.Node()))))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && S#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> M2.__default.Reachable($h0, source#0, sink#0, S#0)
       == M2.__default.Reachable($h1, source#0, sink#0, S#0));

// consequence axiom for M2.__default.Reachable
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box :: 
    { M2.__default.Reachable($Heap, source#0, sink#0, S#0) } 
    M2.__default.Reachable#canCall($Heap, source#0, sink#0, S#0)
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(source#0, Tclass.M2.Node())
           && $Is(sink#0, Tclass.M2.Node())
           && $Is(S#0, TSet(Tclass.M2.Node())))
       ==> true);

function M2.__default.Reachable#requires(Heap, ref, ref, Set Box) : bool;

// #requires axiom for M2.__default.Reachable
axiom (forall $Heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box :: 
  { M2.__default.Reachable#requires($Heap, source#0, sink#0, S#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(source#0, Tclass.M2.Node())
       && $Is(sink#0, Tclass.M2.Node())
       && $Is(S#0, TSet(Tclass.M2.Node()))
     ==> M2.__default.Reachable#requires($Heap, source#0, sink#0, S#0) == true);

// definition axiom for M2.__default.Reachable (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, source#0: ref, sink#0: ref, S#0: Set Box :: 
    { M2.__default.Reachable($Heap, source#0, sink#0, S#0), $IsGoodHeap($Heap) } 
    M2.__default.Reachable#canCall($Heap, source#0, sink#0, S#0)
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(source#0, Tclass.M2.Node())
           && $Is(sink#0, Tclass.M2.Node())
           && $Is(S#0, TSet(Tclass.M2.Node())))
       ==> (forall via#0: DatatypeType :: 
          { M2.__default.ReachableVia($LS($LZ), $Heap, source#0, via#0, sink#0, S#0) } 
          $Is(via#0, Tclass.M2.Path())
             ==> M2.__default.ReachableVia#canCall($Heap, source#0, via#0, sink#0, S#0))
         && M2.__default.Reachable($Heap, source#0, sink#0, S#0)
           == (exists via#0: DatatypeType :: 
            { M2.__default.ReachableVia($LS($LZ), $Heap, source#0, via#0, sink#0, S#0) } 
            $Is(via#0, Tclass.M2.Path())
               && M2.__default.ReachableVia($LS($LZ), $Heap, source#0, via#0, sink#0, S#0)));

procedure CheckWellformed$$M2.__default.Reachable(source#0: ref where $Is(source#0, Tclass.M2.Node()), 
    sink#0: ref where $Is(sink#0, Tclass.M2.Node()), 
    S#0: Set Box where $Is(S#0, TSet(Tclass.M2.Node())));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for M2._default.ReachableVia
function M2.__default.ReachableVia($ly: LayerType, 
    $heap: Heap, 
    source#0: ref, 
    p#0: DatatypeType, 
    sink#0: ref, 
    S#0: Set Box)
   : bool;

function M2.__default.ReachableVia#canCall($heap: Heap, source#0: ref, p#0: DatatypeType, sink#0: ref, S#0: Set Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, 
    $Heap: Heap, 
    source#0: ref, 
    p#0: DatatypeType, 
    sink#0: ref, 
    S#0: Set Box :: 
  { M2.__default.ReachableVia($LS($ly), $Heap, source#0, p#0, sink#0, S#0) } 
  M2.__default.ReachableVia($LS($ly), $Heap, source#0, p#0, sink#0, S#0)
     == M2.__default.ReachableVia($ly, $Heap, source#0, p#0, sink#0, S#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, 
    $Heap: Heap, 
    source#0: ref, 
    p#0: DatatypeType, 
    sink#0: ref, 
    S#0: Set Box :: 
  { M2.__default.ReachableVia(AsFuelBottom($ly), $Heap, source#0, p#0, sink#0, S#0) } 
  M2.__default.ReachableVia($ly, $Heap, source#0, p#0, sink#0, S#0)
     == M2.__default.ReachableVia($LZ, $Heap, source#0, p#0, sink#0, S#0));

// frame axiom for M2.__default.ReachableVia
axiom (forall $ly: LayerType, 
    $h0: Heap, 
    $h1: Heap, 
    source#0: ref, 
    p#0: DatatypeType, 
    sink#0: ref, 
    S#0: Set Box :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), M2.__default.ReachableVia($ly, $h1, source#0, p#0, sink#0, S#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (M2.__default.ReachableVia#canCall($h0, source#0, p#0, sink#0, S#0)
         || (
          $Is(source#0, Tclass.M2.Node())
           && $Is(p#0, Tclass.M2.Path())
           && $Is(sink#0, Tclass.M2.Node())
           && $Is(S#0, TSet(Tclass.M2.Node()))))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && S#0[$Box($o)] ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> M2.__default.ReachableVia($ly, $h0, source#0, p#0, sink#0, S#0)
       == M2.__default.ReachableVia($ly, $h1, source#0, p#0, sink#0, S#0));

// consequence axiom for M2.__default.ReachableVia
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      $Heap: Heap, 
      source#0: ref, 
      p#0: DatatypeType, 
      sink#0: ref, 
      S#0: Set Box :: 
    { M2.__default.ReachableVia($ly, $Heap, source#0, p#0, sink#0, S#0) } 
    M2.__default.ReachableVia#canCall($Heap, source#0, p#0, sink#0, S#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(source#0, Tclass.M2.Node())
           && $Is(p#0, Tclass.M2.Path())
           && $Is(sink#0, Tclass.M2.Node())
           && $Is(S#0, TSet(Tclass.M2.Node())))
       ==> true);

function M2.__default.ReachableVia#requires(LayerType, Heap, ref, DatatypeType, ref, Set Box) : bool;

// #requires axiom for M2.__default.ReachableVia
axiom (forall $ly: LayerType, 
    $Heap: Heap, 
    source#0: ref, 
    p#0: DatatypeType, 
    sink#0: ref, 
    S#0: Set Box :: 
  { M2.__default.ReachableVia#requires($ly, $Heap, source#0, p#0, sink#0, S#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(source#0, Tclass.M2.Node())
       && $Is(p#0, Tclass.M2.Path())
       && $Is(sink#0, Tclass.M2.Node())
       && $Is(S#0, TSet(Tclass.M2.Node()))
     ==> M2.__default.ReachableVia#requires($ly, $Heap, source#0, p#0, sink#0, S#0)
       == true);

// definition axiom for M2.__default.ReachableVia (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      $Heap: Heap, 
      source#0: ref, 
      p#0: DatatypeType, 
      sink#0: ref, 
      S#0: Set Box :: 
    { M2.__default.ReachableVia($LS($ly), $Heap, source#0, p#0, sink#0, S#0), $IsGoodHeap($Heap) } 
    M2.__default.ReachableVia#canCall($Heap, source#0, p#0, sink#0, S#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(source#0, Tclass.M2.Node())
           && $Is(p#0, Tclass.M2.Path())
           && $Is(sink#0, Tclass.M2.Node())
           && $Is(S#0, TSet(Tclass.M2.Node())))
       ==> (!M2.Path.Empty_q(p#0)
           ==> (var n#1 := M2.Path._h1(p#0); 
            (var prefix#1 := M2.Path._h0(p#0); 
              S#0[$Box(n#1)]
                 ==> 
                Seq#Contains(read($Heap, n#1, M2.Node.children), $Box(sink#0))
                 ==> M2.__default.ReachableVia#canCall($Heap, source#0, prefix#1, n#1, S#0))))
         && M2.__default.ReachableVia($LS($ly), $Heap, source#0, p#0, sink#0, S#0)
           == (if M2.Path.Empty_q(p#0)
             then source#0 == sink#0
             else (var n#0 := M2.Path._h1(p#0); 
              (var prefix#0 := M2.Path._h0(p#0); 
                S#0[$Box(n#0)]
                   && Seq#Contains(read($Heap, n#0, M2.Node.children), $Box(sink#0))
                   && M2.__default.ReachableVia($ly, $Heap, source#0, prefix#0, n#0, S#0)))));

procedure CheckWellformed$$M2.__default.ReachableVia(source#0: ref where $Is(source#0, Tclass.M2.Node()), 
    p#0: DatatypeType where $Is(p#0, Tclass.M2.Path()), 
    sink#0: ref where $Is(sink#0, Tclass.M2.Node()), 
    S#0: Set Box where $Is(S#0, TSet(Tclass.M2.Node())));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// Constructor function declaration
function #M2.Path.Empty() : DatatypeType;

const unique ##M2.Path.Empty: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#M2.Path.Empty()) == ##M2.Path.Empty;

function M2.Path.Empty_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { M2.Path.Empty_q(d) } 
  M2.Path.Empty_q(d) <==> DatatypeCtorId(d) == ##M2.Path.Empty);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { M2.Path.Empty_q(d) } 
  M2.Path.Empty_q(d) ==> d == #M2.Path.Empty());

// Constructor $Is
axiom $Is(#M2.Path.Empty(), Tclass.M2.Path());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#M2.Path.Empty(), Tclass.M2.Path(), $h) } 
  $IsGoodHeap($h) ==> $IsAlloc(#M2.Path.Empty(), Tclass.M2.Path(), $h));

// Constructor literal
axiom #M2.Path.Empty() == Lit(#M2.Path.Empty());

// Constructor function declaration
function #M2.Path.Extend(DatatypeType, ref) : DatatypeType;

const unique ##M2.Path.Extend: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: DatatypeType, a#5#1#0: ref :: 
  { #M2.Path.Extend(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#M2.Path.Extend(a#5#0#0, a#5#1#0)) == ##M2.Path.Extend);

function M2.Path.Extend_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { M2.Path.Extend_q(d) } 
  M2.Path.Extend_q(d) <==> DatatypeCtorId(d) == ##M2.Path.Extend);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { M2.Path.Extend_q(d) } 
  M2.Path.Extend_q(d)
     ==> (exists a#6#0#0: DatatypeType, a#6#1#0: ref :: 
      d == #M2.Path.Extend(a#6#0#0, a#6#1#0)));

// Constructor $Is
axiom (forall a#7#0#0: DatatypeType, a#7#1#0: ref :: 
  { $Is(#M2.Path.Extend(a#7#0#0, a#7#1#0), Tclass.M2.Path()) } 
  $Is(#M2.Path.Extend(a#7#0#0, a#7#1#0), Tclass.M2.Path())
     <==> $Is(a#7#0#0, Tclass.M2.Path()) && $Is(a#7#1#0, Tclass.M2.Node()));

// Constructor $IsAlloc
axiom (forall a#8#0#0: DatatypeType, a#8#1#0: ref, $h: Heap :: 
  { $IsAlloc(#M2.Path.Extend(a#8#0#0, a#8#1#0), Tclass.M2.Path(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#M2.Path.Extend(a#8#0#0, a#8#1#0), Tclass.M2.Path(), $h)
       <==> $IsAlloc(a#8#0#0, Tclass.M2.Path(), $h)
         && $IsAlloc(a#8#1#0, Tclass.M2.Node(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(M2.Path._h0(d), Tclass.M2.Path(), $h) } 
  $IsGoodHeap($h) && M2.Path.Extend_q(d) && $IsAlloc(d, Tclass.M2.Path(), $h)
     ==> $IsAlloc(M2.Path._h0(d), Tclass.M2.Path(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(M2.Path._h1(d), Tclass.M2.Node(), $h) } 
  $IsGoodHeap($h) && M2.Path.Extend_q(d) && $IsAlloc(d, Tclass.M2.Path(), $h)
     ==> $IsAlloc(M2.Path._h1(d), Tclass.M2.Node(), $h));

// Constructor literal
axiom (forall a#9#0#0: DatatypeType, a#9#1#0: ref :: 
  { #M2.Path.Extend(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #M2.Path.Extend(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#M2.Path.Extend(a#9#0#0, a#9#1#0)));

function M2.Path._h0(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#10#0#0: DatatypeType, a#10#1#0: ref :: 
  { #M2.Path.Extend(a#10#0#0, a#10#1#0) } 
  M2.Path._h0(#M2.Path.Extend(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: DatatypeType, a#11#1#0: ref :: 
  { #M2.Path.Extend(a#11#0#0, a#11#1#0) } 
  DtRank(a#11#0#0) < DtRank(#M2.Path.Extend(a#11#0#0, a#11#1#0)));

function M2.Path._h1(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#12#0#0: DatatypeType, a#12#1#0: ref :: 
  { #M2.Path.Extend(a#12#0#0, a#12#1#0) } 
  M2.Path._h1(#M2.Path.Extend(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Depth-one case-split function
function $IsA#M2.Path(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#M2.Path(d) } 
  $IsA#M2.Path(d) ==> M2.Path.Empty_q(d) || M2.Path.Extend_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { M2.Path.Extend_q(d), $Is(d, Tclass.M2.Path()) } 
    { M2.Path.Empty_q(d), $Is(d, Tclass.M2.Path()) } 
  $Is(d, Tclass.M2.Path()) ==> M2.Path.Empty_q(d) || M2.Path.Extend_q(d));

// Datatype extensional equality declaration
function M2.Path#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #M2.Path.Empty
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M2.Path#Equal(a, b), M2.Path.Empty_q(a) } 
    { M2.Path#Equal(a, b), M2.Path.Empty_q(b) } 
  M2.Path.Empty_q(a) && M2.Path.Empty_q(b) ==> (M2.Path#Equal(a, b) <==> true));

// Datatype extensional equality definition: #M2.Path.Extend
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M2.Path#Equal(a, b), M2.Path.Extend_q(a) } 
    { M2.Path#Equal(a, b), M2.Path.Extend_q(b) } 
  M2.Path.Extend_q(a) && M2.Path.Extend_q(b)
     ==> (M2.Path#Equal(a, b)
       <==> M2.Path#Equal(M2.Path._h0(a), M2.Path._h0(b))
         && M2.Path._h1(a) == M2.Path._h1(b)));

// Datatype extensionality axiom: M2.Path
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M2.Path#Equal(a, b) } 
  M2.Path#Equal(a, b) <==> a == b);

const unique class.M2.Path: ClassName;

const unique tytagFamily$nat: TyTagFamily;

const unique tytagFamily$object: TyTagFamily;

const unique tytagFamily$array: TyTagFamily;

const unique tytagFamily$_#Func1: TyTagFamily;

const unique tytagFamily$_#PartialFunc1: TyTagFamily;

const unique tytagFamily$_#TotalFunc1: TyTagFamily;

const unique tytagFamily$_#Func0: TyTagFamily;

const unique tytagFamily$_#PartialFunc0: TyTagFamily;

const unique tytagFamily$_#TotalFunc0: TyTagFamily;

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_#Func4: TyTagFamily;

const unique tytagFamily$_#PartialFunc4: TyTagFamily;

const unique tytagFamily$_#TotalFunc4: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$Node: TyTagFamily;

const unique tytagFamily$Path: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$pathFromRoot: NameFamily;

const unique field$children: NameFamily;

const unique field$marked: NameFamily;

const unique field$childrenVisited: NameFamily;
