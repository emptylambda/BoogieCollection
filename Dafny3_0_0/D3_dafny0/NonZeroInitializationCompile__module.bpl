// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy -print:./NonZeroInitializationCompile.bpl

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

procedure CheckWellformed$$_module.MyInt(x#0: int);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.MyInt(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type MyInt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(8,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(6) <= x#0;
    }
    else
    {
        assume true;
        assert LitInt(6) <= LitInt(6);
    }
}



function Tclass._module.MyInt() : Ty;

const unique Tagclass._module.MyInt: TyTag;

// Tclass._module.MyInt Tag
axiom Tag(Tclass._module.MyInt()) == Tagclass._module.MyInt
   && TagFamily(Tclass._module.MyInt()) == tytagFamily$MyInt;

// Box/unbox axiom for Tclass._module.MyInt
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyInt()) } 
  $IsBox(bx, Tclass._module.MyInt())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.MyInt()));

// _module.MyInt: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.MyInt()) } 
  $Is(x#0, Tclass._module.MyInt()) <==> LitInt(6) <= x#0);

// _module.MyInt: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.MyInt(), $h) } 
  $IsAlloc(x#0, Tclass._module.MyInt(), $h));

procedure CheckWellformed$$_module.MyNewInt(x#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.MyNewInt(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype MyNewInt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(9,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(6) <= x#0;
    }
    else
    {
        assume true;
        assert LitInt(6) <= LitInt(12);
    }
}



function Tclass._module.MyNewInt() : Ty;

const unique Tagclass._module.MyNewInt: TyTag;

// Tclass._module.MyNewInt Tag
axiom Tag(Tclass._module.MyNewInt()) == Tagclass._module.MyNewInt
   && TagFamily(Tclass._module.MyNewInt()) == tytagFamily$MyNewInt;

// Box/unbox axiom for Tclass._module.MyNewInt
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyNewInt()) } 
  $IsBox(bx, Tclass._module.MyNewInt())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.MyNewInt()));

// _module.MyNewInt: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.MyNewInt()) } 
  $Is(x#0, Tclass._module.MyNewInt()) <==> LitInt(6) <= x#0);

// _module.MyNewInt: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.MyNewInt(), $h) } 
  $IsAlloc(x#0, Tclass._module.MyNewInt(), $h));

const unique class._module.MyNewInt: ClassName;

procedure CheckWellformed$$_module.short(x#0: int);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.short(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype short
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(11,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(-32768) <= x#0)
        {
        }

        assume LitInt(-32768) <= x#0 && x#0 < 32768;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(-32768) <= LitInt(0);
        assert {:subsumption 0} 0 < 32768;
    }
}



function Tclass._module.short() : Ty;

const unique Tagclass._module.short: TyTag;

// Tclass._module.short Tag
axiom Tag(Tclass._module.short()) == Tagclass._module.short
   && TagFamily(Tclass._module.short()) == tytagFamily$short;

// Box/unbox axiom for Tclass._module.short
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.short()) } 
  $IsBox(bx, Tclass._module.short())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.short()));

// _module.short: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.short()) } 
  $Is(x#0, Tclass._module.short()) <==> LitInt(-32768) <= x#0 && x#0 < 32768);

// _module.short: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.short(), $h) } 
  $IsAlloc(x#0, Tclass._module.short(), $h));

const unique class._module.short: ClassName;

procedure CheckWellformed$$_module.short_k(x#0: int);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.short_k(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype short'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(12,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(-32768) <= x#0)
        {
        }

        assume LitInt(-32768) <= x#0 && x#0 < 32768;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(-32768) <= LitInt(-35);
        assert {:subsumption 0} -35 < 32768;
    }
}



function Tclass._module.short_k() : Ty;

const unique Tagclass._module.short_k: TyTag;

// Tclass._module.short_k Tag
axiom Tag(Tclass._module.short_k()) == Tagclass._module.short_k
   && TagFamily(Tclass._module.short_k()) == tytagFamily$short';

// Box/unbox axiom for Tclass._module.short_k
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.short_k()) } 
  $IsBox(bx, Tclass._module.short_k())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.short_k()));

// _module.short': newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.short_k()) } 
  $Is(x#0, Tclass._module.short_k()) <==> LitInt(-32768) <= x#0 && x#0 < 32768);

// _module.short': newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.short_k(), $h) } 
  $IsAlloc(x#0, Tclass._module.short_k(), $h));

const unique class._module.short_k: ClassName;

procedure CheckWellformed$$_module.FavoriateReals(r#0: real);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.FavoriateReals(r#0: real)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype FavoriateReals
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(14,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (*)
        {
            assume r#0 == LitReal(314e-2);
        }
        else
        {
            assume r#0 != LitReal(314e-2);
            assume r#0 == LitReal(27e-1);
        }
    }
    else
    {
        assume true;
        assert LitReal(314e-2) == LitReal(314e-2) || LitReal(314e-2) == LitReal(27e-1);
    }
}



function Tclass._module.FavoriateReals() : Ty;

const unique Tagclass._module.FavoriateReals: TyTag;

// Tclass._module.FavoriateReals Tag
axiom Tag(Tclass._module.FavoriateReals()) == Tagclass._module.FavoriateReals
   && TagFamily(Tclass._module.FavoriateReals()) == tytagFamily$FavoriateReals;

// Box/unbox axiom for Tclass._module.FavoriateReals
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.FavoriateReals()) } 
  $IsBox(bx, Tclass._module.FavoriateReals())
     ==> $Box($Unbox(bx): real) == bx
       && $Is($Unbox(bx): real, Tclass._module.FavoriateReals()));

// _module.FavoriateReals: newtype $Is
axiom (forall r#0: real :: 
  { $Is(r#0, Tclass._module.FavoriateReals()) } 
  $Is(r#0, Tclass._module.FavoriateReals())
     <==> r#0 == LitReal(314e-2) || r#0 == LitReal(27e-1));

// _module.FavoriateReals: newtype $IsAlloc
axiom (forall r#0: real, $h: Heap :: 
  { $IsAlloc(r#0, Tclass._module.FavoriateReals(), $h) } 
  $IsAlloc(r#0, Tclass._module.FavoriateReals(), $h));

const unique class._module.FavoriateReals: ClassName;

procedure CheckWellformed$$_module.NonEmptyIntSet(s#0: Set Box where $Is(s#0, TSet(TInt)));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NonEmptyIntSet(s#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type NonEmptyIntSet
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(16,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume Set#Card(s#0) != 0;
    }
    else
    {
        assume true;
        assert Set#Card(Lit(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(57))))) != 0;
    }
}



function Tclass._module.NonEmptyIntSet() : Ty;

const unique Tagclass._module.NonEmptyIntSet: TyTag;

// Tclass._module.NonEmptyIntSet Tag
axiom Tag(Tclass._module.NonEmptyIntSet()) == Tagclass._module.NonEmptyIntSet
   && TagFamily(Tclass._module.NonEmptyIntSet()) == tytagFamily$NonEmptyIntSet;

// Box/unbox axiom for Tclass._module.NonEmptyIntSet
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NonEmptyIntSet()) } 
  $IsBox(bx, Tclass._module.NonEmptyIntSet())
     ==> $Box($Unbox(bx): Set Box) == bx
       && $Is($Unbox(bx): Set Box, Tclass._module.NonEmptyIntSet()));

// _module.NonEmptyIntSet: subset type $Is
axiom (forall s#0: Set Box :: 
  { $Is(s#0, Tclass._module.NonEmptyIntSet()) } 
  $Is(s#0, Tclass._module.NonEmptyIntSet())
     <==> $Is(s#0, TSet(TInt)) && Set#Card(s#0) != 0);

// _module.NonEmptyIntSet: subset type $IsAlloc
axiom (forall s#0: Set Box, $h: Heap :: 
  { $IsAlloc(s#0, Tclass._module.NonEmptyIntSet(), $h) } 
  $IsAlloc(s#0, Tclass._module.NonEmptyIntSet(), $h)
     <==> $IsAlloc(s#0, TSet(TInt), $h));

procedure CheckWellformed$$_module.WithTypeParameters(_module.WithTypeParameters$A: Ty, 
    _module.WithTypeParameters$B: Ty, 
    ignoreTypeParams#0: DatatypeType
       where $Is(ignoreTypeParams#0, Tclass._System.Tuple2(TInt, TBool)));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.WithTypeParameters(_module.WithTypeParameters$A: Ty, 
    _module.WithTypeParameters$B: Ty, 
    ignoreTypeParams#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#Z#0: Map Box Box;
  var let#0#0#0: Map Box Box;


    // AddWellformednessCheck for subset type WithTypeParameters
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(19,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume true;
    }
    else
    {
        havoc m#Z#0;
        assume $Is(m#Z#0, TMap(_module.WithTypeParameters$A, _module.WithTypeParameters$B));
        assume let#0#0#0 == Lit(Map#Empty(): Map Box Box);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, TMap(_module.WithTypeParameters$A, _module.WithTypeParameters$B));
        assume m#Z#0 == let#0#0#0;
        if ((var m#0 := Lit(Map#Empty(): Map Box Box); Map#Card(m#0) > 0))
        {
        }
        else
        {
        }

        assume true;
        assert true;
    }
}



function Tclass._module.WithTypeParameters(Ty, Ty) : Ty;

const unique Tagclass._module.WithTypeParameters: TyTag;

// Tclass._module.WithTypeParameters Tag
axiom (forall _module.WithTypeParameters$A: Ty, _module.WithTypeParameters$B: Ty :: 
  { Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B) } 
  Tag(Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B))
       == Tagclass._module.WithTypeParameters
     && TagFamily(Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B))
       == tytagFamily$WithTypeParameters);

// Tclass._module.WithTypeParameters injectivity 0
axiom (forall _module.WithTypeParameters$A: Ty, _module.WithTypeParameters$B: Ty :: 
  { Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B) } 
  Tclass._module.WithTypeParameters_0(Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B))
     == _module.WithTypeParameters$A);

function Tclass._module.WithTypeParameters_0(Ty) : Ty;

// Tclass._module.WithTypeParameters injectivity 1
axiom (forall _module.WithTypeParameters$A: Ty, _module.WithTypeParameters$B: Ty :: 
  { Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B) } 
  Tclass._module.WithTypeParameters_1(Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B))
     == _module.WithTypeParameters$B);

function Tclass._module.WithTypeParameters_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.WithTypeParameters
axiom (forall _module.WithTypeParameters$A: Ty, _module.WithTypeParameters$B: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B)) } 
  $IsBox(bx, 
      Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B)));

// _module.WithTypeParameters: subset type $Is
axiom (forall _module.WithTypeParameters$A: Ty, 
    _module.WithTypeParameters$B: Ty, 
    ignoreTypeParams#0: DatatypeType :: 
  { $Is(ignoreTypeParams#0, 
      Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B)) } 
  $Is(ignoreTypeParams#0, 
      Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B))
     <==> $Is(ignoreTypeParams#0, Tclass._System.Tuple2(TInt, TBool)) && Lit(true));

// _module.WithTypeParameters: subset type $IsAlloc
axiom (forall _module.WithTypeParameters$A: Ty, 
    _module.WithTypeParameters$B: Ty, 
    ignoreTypeParams#0: DatatypeType, 
    $h: Heap :: 
  { $IsAlloc(ignoreTypeParams#0, 
      Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B), 
      $h) } 
  $IsAlloc(ignoreTypeParams#0, 
      Tclass._module.WithTypeParameters(_module.WithTypeParameters$A, _module.WithTypeParameters$B), 
      $h)
     <==> $IsAlloc(ignoreTypeParams#0, Tclass._System.Tuple2(TInt, TBool), $h));

// Constructor function declaration
function #_module.Dt.Atom(int) : DatatypeType;

const unique ##_module.Dt.Atom: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: int :: 
  { #_module.Dt.Atom(a#0#0#0) } 
  DatatypeCtorId(#_module.Dt.Atom(a#0#0#0)) == ##_module.Dt.Atom);

function _module.Dt.Atom_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.Atom_q(d) } 
  _module.Dt.Atom_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.Atom);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.Atom_q(d) } 
  _module.Dt.Atom_q(d) ==> (exists a#1#0#0: int :: d == #_module.Dt.Atom(a#1#0#0)));

function Tclass._module.Dt() : Ty;

const unique Tagclass._module.Dt: TyTag;

// Tclass._module.Dt Tag
axiom Tag(Tclass._module.Dt()) == Tagclass._module.Dt
   && TagFamily(Tclass._module.Dt()) == tytagFamily$Dt;

// Box/unbox axiom for Tclass._module.Dt
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Dt()) } 
  $IsBox(bx, Tclass._module.Dt())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Dt()));

// Constructor $Is
axiom (forall a#2#0#0: int :: 
  { $Is(#_module.Dt.Atom(a#2#0#0), Tclass._module.Dt()) } 
  $Is(#_module.Dt.Atom(a#2#0#0), Tclass._module.Dt())
     <==> $Is(a#2#0#0, Tclass._module.short_k()));

// Constructor $IsAlloc
axiom (forall a#3#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.Dt.Atom(a#3#0#0), Tclass._module.Dt(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dt.Atom(a#3#0#0), Tclass._module.Dt(), $h)
       <==> $IsAlloc(a#3#0#0, Tclass._module.short_k(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt._h0(d), Tclass._module.short_k(), $h) } 
  $IsGoodHeap($h) && _module.Dt.Atom_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt._h0(d), Tclass._module.short_k(), $h));

// Constructor literal
axiom (forall a#4#0#0: int :: 
  { #_module.Dt.Atom(LitInt(a#4#0#0)) } 
  #_module.Dt.Atom(LitInt(a#4#0#0)) == Lit(#_module.Dt.Atom(a#4#0#0)));

function _module.Dt._h0(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#5#0#0: int :: 
  { #_module.Dt.Atom(a#5#0#0) } 
  _module.Dt._h0(#_module.Dt.Atom(a#5#0#0)) == a#5#0#0);

// Constructor function declaration
function #_module.Dt.More(DatatypeType) : DatatypeType;

const unique ##_module.Dt.More: DtCtorId;

// Constructor identifier
axiom (forall a#6#0#0: DatatypeType :: 
  { #_module.Dt.More(a#6#0#0) } 
  DatatypeCtorId(#_module.Dt.More(a#6#0#0)) == ##_module.Dt.More);

function _module.Dt.More_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Dt.More_q(d) } 
  _module.Dt.More_q(d) <==> DatatypeCtorId(d) == ##_module.Dt.More);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Dt.More_q(d) } 
  _module.Dt.More_q(d)
     ==> (exists a#7#0#0: DatatypeType :: d == #_module.Dt.More(a#7#0#0)));

// Constructor $Is
axiom (forall a#8#0#0: DatatypeType :: 
  { $Is(#_module.Dt.More(a#8#0#0), Tclass._module.Dt()) } 
  $Is(#_module.Dt.More(a#8#0#0), Tclass._module.Dt())
     <==> $Is(a#8#0#0, Tclass._module.Dt()));

// Constructor $IsAlloc
axiom (forall a#9#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Dt.More(a#9#0#0), Tclass._module.Dt(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Dt.More(a#9#0#0), Tclass._module.Dt(), $h)
       <==> $IsAlloc(a#9#0#0, Tclass._module.Dt(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Dt._h1(d), Tclass._module.Dt(), $h) } 
  $IsGoodHeap($h) && _module.Dt.More_q(d) && $IsAlloc(d, Tclass._module.Dt(), $h)
     ==> $IsAlloc(_module.Dt._h1(d), Tclass._module.Dt(), $h));

// Constructor literal
axiom (forall a#10#0#0: DatatypeType :: 
  { #_module.Dt.More(Lit(a#10#0#0)) } 
  #_module.Dt.More(Lit(a#10#0#0)) == Lit(#_module.Dt.More(a#10#0#0)));

function _module.Dt._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#11#0#0: DatatypeType :: 
  { #_module.Dt.More(a#11#0#0) } 
  _module.Dt._h1(#_module.Dt.More(a#11#0#0)) == a#11#0#0);

// Inductive rank
axiom (forall a#12#0#0: DatatypeType :: 
  { #_module.Dt.More(a#12#0#0) } 
  DtRank(a#12#0#0) < DtRank(#_module.Dt.More(a#12#0#0)));

// Depth-one case-split function
function $IsA#_module.Dt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Dt(d) } 
  $IsA#_module.Dt(d) ==> _module.Dt.Atom_q(d) || _module.Dt.More_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Dt.More_q(d), $Is(d, Tclass._module.Dt()) } 
    { _module.Dt.Atom_q(d), $Is(d, Tclass._module.Dt()) } 
  $Is(d, Tclass._module.Dt()) ==> _module.Dt.Atom_q(d) || _module.Dt.More_q(d));

// Datatype extensional equality declaration
function _module.Dt#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Dt.Atom
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.Atom_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.Atom_q(b) } 
  _module.Dt.Atom_q(a) && _module.Dt.Atom_q(b)
     ==> (_module.Dt#Equal(a, b) <==> _module.Dt._h0(a) == _module.Dt._h0(b)));

// Datatype extensional equality definition: #_module.Dt.More
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b), _module.Dt.More_q(a) } 
    { _module.Dt#Equal(a, b), _module.Dt.More_q(b) } 
  _module.Dt.More_q(a) && _module.Dt.More_q(b)
     ==> (_module.Dt#Equal(a, b)
       <==> _module.Dt#Equal(_module.Dt._h1(a), _module.Dt._h1(b))));

// Datatype extensionality axiom: _module.Dt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Dt#Equal(a, b) } 
  _module.Dt#Equal(a, b) <==> a == b);

const unique class._module.Dt: ClassName;

const unique class._module.Tr?: ClassName;

function Tclass._module.Tr?() : Ty;

const unique Tagclass._module.Tr?: TyTag;

// Tclass._module.Tr? Tag
axiom Tag(Tclass._module.Tr?()) == Tagclass._module.Tr?
   && TagFamily(Tclass._module.Tr?()) == tytagFamily$Tr;

// Box/unbox axiom for Tclass._module.Tr?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Tr?()) } 
  $IsBox(bx, Tclass._module.Tr?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Tr?()));

// Tr: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Tr?()) } 
  $Is($o, Tclass._module.Tr?())
     <==> $o == null || implements$_module.Tr(dtype($o)));

// Tr: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Tr?(), $h) } 
  $IsAlloc($o, Tclass._module.Tr?(), $h) <==> $o == null || read($h, $o, alloc));

function implements$_module.Tr(Ty) : bool;

axiom FDim(_module.Tr.u) == 0
   && FieldOfDecl(class._module.Tr?, field$u) == _module.Tr.u
   && !$IsGhostField(_module.Tr.u);

const _module.Tr.u: Field int;

// Tr.u: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Tr.u) } 
  $IsGoodHeap($h) && $o != null && $Is($o, Tclass._module.Tr?())
     ==> $Is(read($h, $o, _module.Tr.u), Tclass._module.MyNewInt()));

// Tr.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Tr.u) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && $Is($o, Tclass._module.Tr?())
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Tr.u), Tclass._module.MyNewInt(), $h));

function Tclass._module.Tr() : Ty;

const unique Tagclass._module.Tr: TyTag;

// Tclass._module.Tr Tag
axiom Tag(Tclass._module.Tr()) == Tagclass._module.Tr
   && TagFamily(Tclass._module.Tr()) == tytagFamily$Tr;

// Box/unbox axiom for Tclass._module.Tr
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Tr()) } 
  $IsBox(bx, Tclass._module.Tr())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Tr()));

// _module.Tr: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Tr()) } 
  $Is(c#0, Tclass._module.Tr()) <==> $Is(c#0, Tclass._module.Tr?()) && c#0 != null);

// _module.Tr: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Tr(), $h) } 
  $IsAlloc(c#0, Tclass._module.Tr(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Tr?(), $h));

const unique class._module.MyClass?: ClassName;

function Tclass._module.MyClass?() : Ty;

const unique Tagclass._module.MyClass?: TyTag;

// Tclass._module.MyClass? Tag
axiom Tag(Tclass._module.MyClass?()) == Tagclass._module.MyClass?
   && TagFamily(Tclass._module.MyClass?()) == tytagFamily$MyClass;

// Box/unbox axiom for Tclass._module.MyClass?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyClass?()) } 
  $IsBox(bx, Tclass._module.MyClass?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.MyClass?()));

// MyClass: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.MyClass?()) } 
  $Is($o, Tclass._module.MyClass?())
     <==> $o == null || dtype($o) == Tclass._module.MyClass?());

// MyClass: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.MyClass?(), $h) } 
  $IsAlloc($o, Tclass._module.MyClass?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom implements$_module.Tr(Tclass._module.MyClass?());

axiom FDim(_module.MyClass.x) == 0
   && FieldOfDecl(class._module.MyClass?, field$x) == _module.MyClass.x
   && !$IsGhostField(_module.MyClass.x);

const _module.MyClass.x: Field int;

// MyClass.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyClass?()
     ==> $Is(read($h, $o, _module.MyClass.x), TInt));

// MyClass.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyClass.x), TInt, $h));

axiom FDim(_module.MyClass.r) == 0
   && FieldOfDecl(class._module.MyClass?, field$r) == _module.MyClass.r
   && !$IsGhostField(_module.MyClass.r);

const _module.MyClass.r: Field real;

// MyClass.r: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.r) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyClass?()
     ==> $Is(read($h, $o, _module.MyClass.r), Tclass._module.FavoriateReals()));

// MyClass.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.r) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyClass.r), Tclass._module.FavoriateReals(), $h));

axiom FDim(_module.MyClass.nes) == 0
   && FieldOfDecl(class._module.MyClass?, field$nes) == _module.MyClass.nes
   && !$IsGhostField(_module.MyClass.nes);

const _module.MyClass.nes: Field (Set Box);

// MyClass.nes: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.nes) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyClass?()
     ==> $Is(read($h, $o, _module.MyClass.nes), Tclass._module.NonEmptyIntSet()));

// MyClass.nes: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClass.nes) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClass?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyClass.nes), Tclass._module.NonEmptyIntSet(), $h));

function Tclass._module.MyClass() : Ty;

const unique Tagclass._module.MyClass: TyTag;

// Tclass._module.MyClass Tag
axiom Tag(Tclass._module.MyClass()) == Tagclass._module.MyClass
   && TagFamily(Tclass._module.MyClass()) == tytagFamily$MyClass;

// Box/unbox axiom for Tclass._module.MyClass
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyClass()) } 
  $IsBox(bx, Tclass._module.MyClass())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.MyClass()));

// _module.MyClass: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.MyClass()) } 
  $Is(c#0, Tclass._module.MyClass())
     <==> $Is(c#0, Tclass._module.MyClass?()) && c#0 != null);

// _module.MyClass: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.MyClass(), $h) } 
  $IsAlloc(c#0, Tclass._module.MyClass(), $h)
     <==> $IsAlloc(c#0, Tclass._module.MyClass?(), $h));

const unique class._module.MyClassWithCtor?: ClassName;

function Tclass._module.MyClassWithCtor?() : Ty;

const unique Tagclass._module.MyClassWithCtor?: TyTag;

// Tclass._module.MyClassWithCtor? Tag
axiom Tag(Tclass._module.MyClassWithCtor?()) == Tagclass._module.MyClassWithCtor?
   && TagFamily(Tclass._module.MyClassWithCtor?()) == tytagFamily$MyClassWithCtor;

// Box/unbox axiom for Tclass._module.MyClassWithCtor?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyClassWithCtor?()) } 
  $IsBox(bx, Tclass._module.MyClassWithCtor?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyClassWithCtor?()));

// MyClassWithCtor: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.MyClassWithCtor?()) } 
  $Is($o, Tclass._module.MyClassWithCtor?())
     <==> $o == null || dtype($o) == Tclass._module.MyClassWithCtor?());

// MyClassWithCtor: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.MyClassWithCtor?(), $h) } 
  $IsAlloc($o, Tclass._module.MyClassWithCtor?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom implements$_module.Tr(Tclass._module.MyClassWithCtor?());

axiom FDim(_module.MyClassWithCtor.x) == 0
   && FieldOfDecl(class._module.MyClassWithCtor?, field$x)
     == _module.MyClassWithCtor.x
   && !$IsGhostField(_module.MyClassWithCtor.x);

const _module.MyClassWithCtor.x: Field int;

// MyClassWithCtor.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClassWithCtor.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyClassWithCtor?()
     ==> $Is(read($h, $o, _module.MyClassWithCtor.x), TInt));

// MyClassWithCtor.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClassWithCtor.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClassWithCtor?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyClassWithCtor.x), TInt, $h));

axiom FDim(_module.MyClassWithCtor.r) == 0
   && FieldOfDecl(class._module.MyClassWithCtor?, field$r)
     == _module.MyClassWithCtor.r
   && !$IsGhostField(_module.MyClassWithCtor.r);

const _module.MyClassWithCtor.r: Field real;

// MyClassWithCtor.r: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClassWithCtor.r) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyClassWithCtor?()
     ==> $Is(read($h, $o, _module.MyClassWithCtor.r), Tclass._module.FavoriateReals()));

// MyClassWithCtor.r: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClassWithCtor.r) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClassWithCtor?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyClassWithCtor.r), Tclass._module.FavoriateReals(), $h));

axiom FDim(_module.MyClassWithCtor.nes) == 0
   && FieldOfDecl(class._module.MyClassWithCtor?, field$nes)
     == _module.MyClassWithCtor.nes
   && !$IsGhostField(_module.MyClassWithCtor.nes);

const _module.MyClassWithCtor.nes: Field (Set Box);

// MyClassWithCtor.nes: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClassWithCtor.nes) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.MyClassWithCtor?()
     ==> $Is(read($h, $o, _module.MyClassWithCtor.nes), Tclass._module.NonEmptyIntSet()));

// MyClassWithCtor.nes: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.MyClassWithCtor.nes) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.MyClassWithCtor?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.MyClassWithCtor.nes), Tclass._module.NonEmptyIntSet(), $h));

function Tclass._module.MyClassWithCtor() : Ty;

const unique Tagclass._module.MyClassWithCtor: TyTag;

// Tclass._module.MyClassWithCtor Tag
axiom Tag(Tclass._module.MyClassWithCtor()) == Tagclass._module.MyClassWithCtor
   && TagFamily(Tclass._module.MyClassWithCtor()) == tytagFamily$MyClassWithCtor;

// Box/unbox axiom for Tclass._module.MyClassWithCtor
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyClassWithCtor()) } 
  $IsBox(bx, Tclass._module.MyClassWithCtor())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.MyClassWithCtor()));

procedure CheckWellformed$$_module.MyClassWithCtor.Init(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClassWithCtor())
         && $IsAlloc(this, Tclass._module.MyClassWithCtor(), $Heap), 
    y#0: int);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.MyClassWithCtor.Init(y#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.MyClassWithCtor())
         && $IsAlloc(this, Tclass._module.MyClassWithCtor(), $Heap));
  modifies $Heap, $Tick;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.MyClassWithCtor.Init(y#0: int)
   returns (this: ref where this != null && $Is(this, Tclass._module.MyClassWithCtor()), 
    $_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.MyClassWithCtor.Init(y#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.u: int;
  var this.x: int;
  var this.r: real;
  var this.nes: Set Box;
  var $rhs#0: Set Box where $Is($rhs#0, Tclass._module.NonEmptyIntSet());

    // AddMethodImpl: Init, Impl$$_module.MyClassWithCtor.Init
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(39,2): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(39,3)
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(39,3)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Tr.u) == this.u;
    assume read($Heap, this, _module.MyClassWithCtor.x) == this.x;
    assume read($Heap, this, _module.MyClassWithCtor.r) == this.r;
    assume read($Heap, this, _module.MyClassWithCtor.nes) == this.nes;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(39,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(41,9)
    assume true;
    assert $_Frame[this, _module.MyClassWithCtor.nes];
    assume true;
    assert $Is(Set#Union(read($Heap, this, _module.MyClassWithCtor.nes), 
        Set#UnionOne(Set#Empty(): Set Box, $Box(y#0))), 
      Tclass._module.NonEmptyIntSet());
    $rhs#0 := Set#Union(read($Heap, this, _module.MyClassWithCtor.nes), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(y#0)));
    $Heap := update($Heap, this, _module.MyClassWithCtor.nes, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(41,20)"} true;
}



// _module.MyClassWithCtor: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.MyClassWithCtor()) } 
  $Is(c#0, Tclass._module.MyClassWithCtor())
     <==> $Is(c#0, Tclass._module.MyClassWithCtor?()) && c#0 != null);

// _module.MyClassWithCtor: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.MyClassWithCtor(), $h) } 
  $IsAlloc(c#0, Tclass._module.MyClassWithCtor(), $h)
     <==> $IsAlloc(c#0, Tclass._module.MyClassWithCtor?(), $h));

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

procedure CheckWellformed$$_module.__default._default_Main();
  free requires 13 == $FunctionContextHeight;
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
  free requires 13 == $FunctionContextHeight;
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
  var m#0: int where LitInt(6) <= m#0;
  var n#0: int where LitInt(6) <= n#0;
  var newtype$check#0: int;
  var s#0: int where LitInt(-32768) <= s#0 && s#0 < 32768;
  var s'#0: int where LitInt(-32768) <= s'#0 && s'#0 < 32768;
  var nes#0: Set Box
     where $Is(nes#0, Tclass._module.NonEmptyIntSet())
       && $IsAlloc(nes#0, Tclass._module.NonEmptyIntSet(), $Heap);
  var S##0: Set Box;
  var f0#0: DatatypeType
     where $Is(f0#0, Tclass._System.Tuple2(TInt, TBool))
       && $IsAlloc(f0#0, Tclass._System.Tuple2(TInt, TBool), $Heap);
  var f1#0: DatatypeType
     where $Is(f1#0, Tclass._module.WithTypeParameters(TInt, TBool))
       && $IsAlloc(f1#0, Tclass._module.WithTypeParameters(TInt, TBool), $Heap);
  var dt#0: DatatypeType
     where $Is(dt#0, Tclass._module.Dt()) && $IsAlloc(dt#0, Tclass._module.Dt(), $Heap);
  var cl#0: ref
     where $Is(cl#0, Tclass._module.MyClass())
       && $IsAlloc(cl#0, Tclass._module.MyClass(), $Heap);
  var $nw: ref;
  var S##1: Set Box;
  var cl'#0: ref
     where $Is(cl'#0, Tclass._module.MyClassWithCtor())
       && $IsAlloc(cl'#0, Tclass._module.MyClassWithCtor(), $Heap);
  var y##0: int;
  var S##2: Set Box;
  var which##0: int;
  var which##1: int;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(46,0): initial state"} true;
    $_reverifyPost := false;
    havoc m#0 /* where LitInt(6) <= m#0 */;
    havoc n#0 /* where LitInt(6) <= n#0 */;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(49,3)
    if (LitInt(6) <= m#0)
    {
        newtype$check#0 := LitInt(6);
        assert LitInt(6) <= newtype$check#0;
    }

    assume true;
    assert {:subsumption 0} LitInt(6) <= m#0;
    assert {:subsumption 0} LitInt(6) <= n#0;
    assume LitInt(6) <= m#0 && LitInt(6) <= n#0;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(50,3)
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    havoc s#0 /* where LitInt(-32768) <= s#0 && s#0 < 32768 */, s'#0 /* where LitInt(-32768) <= s'#0 && s'#0 < 32768 */;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(52,3)
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    havoc nes#0 /* where $Is(nes#0, Tclass._module.NonEmptyIntSet())
       && $IsAlloc(nes#0, Tclass._module.NonEmptyIntSet(), $Heap) */;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(54,3)
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(54,26)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##0 := nes#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintSet(S##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(54,30)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(54,33)
    assume true;
    havoc f0#0 /* where $Is(f0#0, Tclass._System.Tuple2(TInt, TBool))
       && $IsAlloc(f0#0, Tclass._System.Tuple2(TInt, TBool), $Heap) */, f1#0 /* where $Is(f1#0, Tclass._module.WithTypeParameters(TInt, TBool))
       && $IsAlloc(f1#0, Tclass._module.WithTypeParameters(TInt, TBool), $Heap) */;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(56,3)
    assume true;
    assume true;
    assume true;
    assume true;
    assume true;
    havoc dt#0 /* where $Is(dt#0, Tclass._module.Dt()) && $IsAlloc(dt#0, Tclass._module.Dt(), $Heap) */;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(58,3)
    assume true;
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(59,10)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.MyClass?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    cl#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(59,23)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(60,3)
    assume true;
    assert {:subsumption 0} cl#0 != null;
    assume true;
    assume true;
    assert {:subsumption 0} cl#0 != null;
    assume true;
    assume true;
    assert {:subsumption 0} cl#0 != null;
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(60,76)
    // TrCallStmt: Before ProcessCallStmt
    assert cl#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##1 := read($Heap, cl#0, _module.MyClass.nes);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintSet(S##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(60,83)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(60,86)
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(61,11)
    assume true;
    // ----- init call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(61,34)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := LitInt(20);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.MyClassWithCtor.Init(y##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(61,41)"} true;
    cl'#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(61,41)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(62,3)
    assume true;
    assert {:subsumption 0} cl'#0 != null;
    assume true;
    assume true;
    assert {:subsumption 0} cl'#0 != null;
    assume true;
    assume true;
    assert {:subsumption 0} cl'#0 != null;
    assume true;
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(62,80)
    // TrCallStmt: Before ProcessCallStmt
    assert cl'#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    S##2 := read($Heap, cl'#0, _module.MyClassWithCtor.nes);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintSet(S##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(62,88)"} true;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(62,91)
    assume true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(63,34)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    which##0 := LitInt(0);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$AdvancedZeroInitialization.__default.Test(which##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(63,36)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(64,34)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    which##1 := LitInt(1);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$AdvancedZeroInitialization.__default.Test(which##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(64,36)"} true;
}



procedure CheckWellformed$$_module.__default.PrintSet(S#0: Set Box where $Is(S#0, TSet(TInt)) && $IsAlloc(S#0, TSet(TInt), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.PrintSet(S#0: Set Box where $Is(S#0, TSet(TInt)) && $IsAlloc(S#0, TSet(TInt), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.PrintSet(S#0: Set Box where $Is(S#0, TSet(TInt)) && $IsAlloc(S#0, TSet(TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.PrintSet(S#0: Set Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap);
  var sep#0: Seq Box
     where $Is(sep#0, TSeq(TChar)) && $IsAlloc(sep#0, TSeq(TChar), $Heap);
  var $rhs#0: Set Box where $Is($rhs#0, TSet(TInt));
  var $rhs#1: Seq Box where $Is($rhs#1, TSeq(TChar));
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var m#0_0: int;
  var $rhs##0_0: int;
  var s##0_0: Set Box;
  var x#0_0: int;
  var x#0_1: int;
  var y#0_0: int;
  var $rhs#0_0: Set Box where $Is($rhs#0_0, TSet(TInt));
  var $rhs#0_1: Seq Box where $Is($rhs#0_1, TSeq(TChar));

    // AddMethodImpl: PrintSet, Impl$$_module.__default.PrintSet
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(128,29): initial state"} true;
    $_reverifyPost := false;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(129,3)
    assume true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(130,24)
    assume true;
    assume true;
    assume true;
    $rhs#0 := S#0;
    assume true;
    $rhs#1 := Lit(Seq#Empty(): Seq Box);
    s#0 := $rhs#0;
    sep#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(130,31)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(131,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := (if Set#Card(s#0) <= LitInt(0) then 0 - Set#Card(s#0) else Set#Card(s#0) - 0);
    havoc $w$loop#0;
    while (true)
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant (if Set#Card(s#0) <= LitInt(0) then 0 - Set#Card(s#0) else Set#Card(s#0) - 0)
           <= $decr_init$loop#00
         && ((if Set#Card(s#0) <= LitInt(0) then 0 - Set#Card(s#0) else Set#Card(s#0) - 0)
             == $decr_init$loop#00
           ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(131,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (Set#Card(s#0) <= LitInt(0))
            {
            }
            else
            {
            }

            assume true;
            assume false;
        }

        assume true;
        if (Set#Card(s#0) == 0)
        {
            break;
        }

        $decr$loop#00 := (if Set#Card(s#0) <= LitInt(0) then 0 - Set#Card(s#0) else Set#Card(s#0) - 0);
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(132,5)
        assume true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(134,36)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0_0 := s#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.__default.ThereIsASmallest(s##0_0);
        // TrCallStmt: After ProcessCallStmt
        m#0_0 := $rhs##0_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(134,38)"} true;
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(135,11)
        havoc x#0_1;
        if (true)
        {
            if (s#0[$Box(x#0_1)])
            {
                // Begin Comprehension WF check
                havoc y#0_0;
                if (true)
                {
                    if (s#0[$Box(y#0_0)])
                    {
                    }
                }

                // End Comprehension WF check
            }

            assume true;
        }

        assert ($Is(LitInt(0), TInt)
             && 
            s#0[$Box(LitInt(0))]
             && (forall y#0_3: int :: 
              { s#0[$Box(y#0_3)] } 
              true ==> s#0[$Box(y#0_3)] ==> LitInt(0) <= y#0_3))
           || (exists $as#x0_0#0_0: int :: 
            s#0[$Box($as#x0_0#0_0)]
               && (forall y#0_2: int :: 
                { s#0[$Box(y#0_2)] } 
                true ==> s#0[$Box(y#0_2)] ==> $as#x0_0#0_0 <= y#0_2));
        havoc x#0_0;
        assume s#0[$Box(x#0_0)]
           && (forall y#0_4: int :: 
            { s#0[$Box(y#0_4)] } 
            true ==> s#0[$Box(y#0_4)] ==> x#0_0 <= y#0_4);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(135,52)"} true;
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(136,5)
        assume true;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(137,12)
        assume true;
        assume true;
        assume true;
        $rhs#0_0 := Set#Difference(s#0, Set#UnionOne(Set#Empty(): Set Box, $Box(x#0_0)));
        assume true;
        $rhs#0_1 := Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(44))), $Box(char#FromInt(32))));
        s#0 := $rhs#0_0;
        sep#0 := $rhs#0_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(137,27)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(131,3)
        assert 0 <= $decr$loop#00
           || (if Set#Card(s#0) <= LitInt(0) then 0 - Set#Card(s#0) else Set#Card(s#0) - 0)
             == $decr$loop#00;
        assert (if Set#Card(s#0) <= LitInt(0) then 0 - Set#Card(s#0) else Set#Card(s#0) - 0)
           < $decr$loop#00;
    }

    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(139,3)
    assume true;
}



procedure CheckWellformed$$_module.__default.ThereIsASmallest(s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (m#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ThereIsASmallest(s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (m#0: int);
  // user-defined preconditions
  requires !Set#Equal(s#0, Set#Empty(): Set Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures s#0[$Box(m#0)];
  ensures (forall y#1: int :: { s#0[$Box(y#1)] } true ==> s#0[$Box(y#1)] ==> m#0 <= y#1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.ThereIsASmallest(s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap))
   returns (m#0: int, $_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  // user-defined preconditions
  requires !Set#Equal(s#0, Set#Empty(): Set Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures s#0[$Box(m#0)];
  ensures (forall y#1: int :: { s#0[$Box(y#1)] } true ==> s#0[$Box(y#1)] ==> m#0 <= y#1);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.ThereIsASmallest(s#0: Set Box) returns (m#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m#1: int;
  var eg$y#0: int;
  var y#0_0: int;
  var s'#0_0: Set Box
     where $Is(s'#0_0, TSet(TInt)) && $IsAlloc(s'#0_0, TSet(TInt), $Heap);
  var $rhs##0_0: int;
  var s##0_0: Set Box;

    // AddMethodImpl: ThereIsASmallest, Impl$$_module.__default.ThereIsASmallest
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(145,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(146,5)
    havoc m#1;
    if (true)
    {
        assume true;
    }

    assert ($Is(LitInt(0), TInt) && s#0[$Box(LitInt(0))])
       || (exists $as#m0#0: int :: s#0[$Box($as#m0#0)]);
    havoc m#0;
    assume s#0[$Box(m#0)];
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(146,13)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(147,3)
    // Begin Comprehension WF check
    havoc eg$y#0;
    if (true)
    {
        if (s#0[$Box(eg$y#0)])
        {
        }
    }

    // End Comprehension WF check
    assume true;
    havoc y#0_0;
    if (*)
    {
        assume s#0[$Box(y#0_0)] && y#0_0 < m#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(148,12)
        assume true;
        assume true;
        s'#0_0 := Set#Difference(s#0, Set#UnionOne(Set#Empty(): Set Box, $Box(m#0)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(148,21)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(149,5)
        assume true;
        assert Set#Equal(s#0, Set#Union(s'#0_0, Set#UnionOne(Set#Empty(): Set Box, $Box(m#0))));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(150,5)
        assume true;
        assert s'#0_0[$Box(y#0_0)];
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(151,26)
        assume true;
        // TrCallStmt: Adding lhs with type int
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0_0 := s'#0_0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert Set#Subset(s##0_0, s#0) && !Set#Subset(s#0, s##0_0);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.__default.ThereIsASmallest(s##0_0);
        // TrCallStmt: After ProcessCallStmt
        m#0 := $rhs##0_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitializationCompile.dfy(151,29)"} true;
    }
    else
    {
        assume !(exists eg$y#1: int :: s#0[$Box(eg$y#1)] && eg$y#1 < m#0);
    }
}



// Constructor function declaration
function #AdvancedZeroInitialization.Xt.MakeXt(int, Seq Box) : DatatypeType;

const unique ##AdvancedZeroInitialization.Xt.MakeXt: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: int, a#0#1#0: Seq Box :: 
  { #AdvancedZeroInitialization.Xt.MakeXt(a#0#0#0, a#0#1#0) } 
  DatatypeCtorId(#AdvancedZeroInitialization.Xt.MakeXt(a#0#0#0, a#0#1#0))
     == ##AdvancedZeroInitialization.Xt.MakeXt);

function AdvancedZeroInitialization.Xt.MakeXt_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { AdvancedZeroInitialization.Xt.MakeXt_q(d) } 
  AdvancedZeroInitialization.Xt.MakeXt_q(d)
     <==> DatatypeCtorId(d) == ##AdvancedZeroInitialization.Xt.MakeXt);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { AdvancedZeroInitialization.Xt.MakeXt_q(d) } 
  AdvancedZeroInitialization.Xt.MakeXt_q(d)
     ==> (exists a#1#0#0: int, a#1#1#0: Seq Box :: 
      d == #AdvancedZeroInitialization.Xt.MakeXt(a#1#0#0, a#1#1#0)));

function Tclass.AdvancedZeroInitialization.Xt() : Ty;

const unique Tagclass.AdvancedZeroInitialization.Xt: TyTag;

// Tclass.AdvancedZeroInitialization.Xt Tag
axiom Tag(Tclass.AdvancedZeroInitialization.Xt())
     == Tagclass.AdvancedZeroInitialization.Xt
   && TagFamily(Tclass.AdvancedZeroInitialization.Xt()) == tytagFamily$Xt;

// Box/unbox axiom for Tclass.AdvancedZeroInitialization.Xt
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AdvancedZeroInitialization.Xt()) } 
  $IsBox(bx, Tclass.AdvancedZeroInitialization.Xt())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.AdvancedZeroInitialization.Xt()));

// Constructor $Is
axiom (forall a#2#0#0: int, a#2#1#0: Seq Box :: 
  { $Is(#AdvancedZeroInitialization.Xt.MakeXt(a#2#0#0, a#2#1#0), 
      Tclass.AdvancedZeroInitialization.Xt()) } 
  $Is(#AdvancedZeroInitialization.Xt.MakeXt(a#2#0#0, a#2#1#0), 
      Tclass.AdvancedZeroInitialization.Xt())
     <==> $Is(a#2#0#0, TInt) && $Is(a#2#1#0, TSeq(TInt)));

// Constructor $IsAlloc
axiom (forall a#3#0#0: int, a#3#1#0: Seq Box, $h: Heap :: 
  { $IsAlloc(#AdvancedZeroInitialization.Xt.MakeXt(a#3#0#0, a#3#1#0), 
      Tclass.AdvancedZeroInitialization.Xt(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#AdvancedZeroInitialization.Xt.MakeXt(a#3#0#0, a#3#1#0), 
        Tclass.AdvancedZeroInitialization.Xt(), 
        $h)
       <==> $IsAlloc(a#3#0#0, TInt, $h) && $IsAlloc(a#3#1#0, TSeq(TInt), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(AdvancedZeroInitialization.Xt.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      AdvancedZeroInitialization.Xt.MakeXt_q(d)
       && $IsAlloc(d, Tclass.AdvancedZeroInitialization.Xt(), $h)
     ==> $IsAlloc(AdvancedZeroInitialization.Xt.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(AdvancedZeroInitialization.Xt.s(d), TSeq(TInt), $h) } 
  $IsGoodHeap($h)
       && 
      AdvancedZeroInitialization.Xt.MakeXt_q(d)
       && $IsAlloc(d, Tclass.AdvancedZeroInitialization.Xt(), $h)
     ==> $IsAlloc(AdvancedZeroInitialization.Xt.s(d), TSeq(TInt), $h));

// Constructor literal
axiom (forall a#4#0#0: int, a#4#1#0: Seq Box :: 
  { #AdvancedZeroInitialization.Xt.MakeXt(LitInt(a#4#0#0), Lit(a#4#1#0)) } 
  #AdvancedZeroInitialization.Xt.MakeXt(LitInt(a#4#0#0), Lit(a#4#1#0))
     == Lit(#AdvancedZeroInitialization.Xt.MakeXt(a#4#0#0, a#4#1#0)));

function AdvancedZeroInitialization.Xt.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#5#0#0: int, a#5#1#0: Seq Box :: 
  { #AdvancedZeroInitialization.Xt.MakeXt(a#5#0#0, a#5#1#0) } 
  AdvancedZeroInitialization.Xt.x(#AdvancedZeroInitialization.Xt.MakeXt(a#5#0#0, a#5#1#0))
     == a#5#0#0);

function AdvancedZeroInitialization.Xt.s(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#6#0#0: int, a#6#1#0: Seq Box :: 
  { #AdvancedZeroInitialization.Xt.MakeXt(a#6#0#0, a#6#1#0) } 
  AdvancedZeroInitialization.Xt.s(#AdvancedZeroInitialization.Xt.MakeXt(a#6#0#0, a#6#1#0))
     == a#6#1#0);

// Inductive seq element rank
axiom (forall a#7#0#0: int, a#7#1#0: Seq Box, i: int :: 
  { Seq#Index(a#7#1#0, i), #AdvancedZeroInitialization.Xt.MakeXt(a#7#0#0, a#7#1#0) } 
  0 <= i && i < Seq#Length(a#7#1#0)
     ==> DtRank($Unbox(Seq#Index(a#7#1#0, i)): DatatypeType)
       < DtRank(#AdvancedZeroInitialization.Xt.MakeXt(a#7#0#0, a#7#1#0)));

// Inductive seq rank
axiom (forall a#8#0#0: int, a#8#1#0: Seq Box :: 
  { #AdvancedZeroInitialization.Xt.MakeXt(a#8#0#0, a#8#1#0) } 
  Seq#Rank(a#8#1#0)
     < DtRank(#AdvancedZeroInitialization.Xt.MakeXt(a#8#0#0, a#8#1#0)));

// Depth-one case-split function
function $IsA#AdvancedZeroInitialization.Xt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#AdvancedZeroInitialization.Xt(d) } 
  $IsA#AdvancedZeroInitialization.Xt(d)
     ==> AdvancedZeroInitialization.Xt.MakeXt_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { AdvancedZeroInitialization.Xt.MakeXt_q(d), $Is(d, Tclass.AdvancedZeroInitialization.Xt()) } 
  $Is(d, Tclass.AdvancedZeroInitialization.Xt())
     ==> AdvancedZeroInitialization.Xt.MakeXt_q(d));

// Datatype extensional equality declaration
function AdvancedZeroInitialization.Xt#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #AdvancedZeroInitialization.Xt.MakeXt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { AdvancedZeroInitialization.Xt#Equal(a, b) } 
  true
     ==> (AdvancedZeroInitialization.Xt#Equal(a, b)
       <==> AdvancedZeroInitialization.Xt.x(a) == AdvancedZeroInitialization.Xt.x(b)
         && Seq#Equal(AdvancedZeroInitialization.Xt.s(a), AdvancedZeroInitialization.Xt.s(b))));

// Datatype extensionality axiom: AdvancedZeroInitialization.Xt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { AdvancedZeroInitialization.Xt#Equal(a, b) } 
  AdvancedZeroInitialization.Xt#Equal(a, b) <==> a == b);

const unique class.AdvancedZeroInitialization.Xt: ClassName;

// Constructor function declaration
function #AdvancedZeroInitialization.Yt.MakeYt(int, Box) : DatatypeType;

const unique ##AdvancedZeroInitialization.Yt.MakeYt: DtCtorId;

// Constructor identifier
axiom (forall a#9#0#0: int, a#9#1#0: Box :: 
  { #AdvancedZeroInitialization.Yt.MakeYt(a#9#0#0, a#9#1#0) } 
  DatatypeCtorId(#AdvancedZeroInitialization.Yt.MakeYt(a#9#0#0, a#9#1#0))
     == ##AdvancedZeroInitialization.Yt.MakeYt);

function AdvancedZeroInitialization.Yt.MakeYt_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { AdvancedZeroInitialization.Yt.MakeYt_q(d) } 
  AdvancedZeroInitialization.Yt.MakeYt_q(d)
     <==> DatatypeCtorId(d) == ##AdvancedZeroInitialization.Yt.MakeYt);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { AdvancedZeroInitialization.Yt.MakeYt_q(d) } 
  AdvancedZeroInitialization.Yt.MakeYt_q(d)
     ==> (exists a#10#0#0: int, a#10#1#0: Box :: 
      d == #AdvancedZeroInitialization.Yt.MakeYt(a#10#0#0, a#10#1#0)));

function Tclass.AdvancedZeroInitialization.Yt(Ty) : Ty;

const unique Tagclass.AdvancedZeroInitialization.Yt: TyTag;

// Tclass.AdvancedZeroInitialization.Yt Tag
axiom (forall AdvancedZeroInitialization.Yt$Y: Ty :: 
  { Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y) } 
  Tag(Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y))
       == Tagclass.AdvancedZeroInitialization.Yt
     && TagFamily(Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y))
       == tytagFamily$Yt);

// Tclass.AdvancedZeroInitialization.Yt injectivity 0
axiom (forall AdvancedZeroInitialization.Yt$Y: Ty :: 
  { Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y) } 
  Tclass.AdvancedZeroInitialization.Yt_0(Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y))
     == AdvancedZeroInitialization.Yt$Y);

function Tclass.AdvancedZeroInitialization.Yt_0(Ty) : Ty;

// Box/unbox axiom for Tclass.AdvancedZeroInitialization.Yt
axiom (forall AdvancedZeroInitialization.Yt$Y: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y)) } 
  $IsBox(bx, Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y)));

// Constructor $Is
axiom (forall AdvancedZeroInitialization.Yt$Y: Ty, a#11#0#0: int, a#11#1#0: Box :: 
  { $Is(#AdvancedZeroInitialization.Yt.MakeYt(a#11#0#0, a#11#1#0), 
      Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y)) } 
  $Is(#AdvancedZeroInitialization.Yt.MakeYt(a#11#0#0, a#11#1#0), 
      Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y))
     <==> $Is(a#11#0#0, TInt) && $IsBox(a#11#1#0, AdvancedZeroInitialization.Yt$Y));

// Constructor $IsAlloc
axiom (forall AdvancedZeroInitialization.Yt$Y: Ty, a#12#0#0: int, a#12#1#0: Box, $h: Heap :: 
  { $IsAlloc(#AdvancedZeroInitialization.Yt.MakeYt(a#12#0#0, a#12#1#0), 
      Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#AdvancedZeroInitialization.Yt.MakeYt(a#12#0#0, a#12#1#0), 
        Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y), 
        $h)
       <==> $IsAlloc(a#12#0#0, TInt, $h)
         && $IsAllocBox(a#12#1#0, AdvancedZeroInitialization.Yt$Y, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(AdvancedZeroInitialization.Yt.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      AdvancedZeroInitialization.Yt.MakeYt_q(d)
       && (exists AdvancedZeroInitialization.Yt$Y: Ty :: 
        { $IsAlloc(d, Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y), $h) } 
        $IsAlloc(d, Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y), $h))
     ==> $IsAlloc(AdvancedZeroInitialization.Yt.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, AdvancedZeroInitialization.Yt$Y: Ty, $h: Heap :: 
  { $IsAllocBox(AdvancedZeroInitialization.Yt.y(d), AdvancedZeroInitialization.Yt$Y, $h) } 
  $IsGoodHeap($h)
       && 
      AdvancedZeroInitialization.Yt.MakeYt_q(d)
       && $IsAlloc(d, Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y), $h)
     ==> $IsAllocBox(AdvancedZeroInitialization.Yt.y(d), AdvancedZeroInitialization.Yt$Y, $h));

// Constructor literal
axiom (forall a#13#0#0: int, a#13#1#0: Box :: 
  { #AdvancedZeroInitialization.Yt.MakeYt(LitInt(a#13#0#0), Lit(a#13#1#0)) } 
  #AdvancedZeroInitialization.Yt.MakeYt(LitInt(a#13#0#0), Lit(a#13#1#0))
     == Lit(#AdvancedZeroInitialization.Yt.MakeYt(a#13#0#0, a#13#1#0)));

function AdvancedZeroInitialization.Yt.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#14#0#0: int, a#14#1#0: Box :: 
  { #AdvancedZeroInitialization.Yt.MakeYt(a#14#0#0, a#14#1#0) } 
  AdvancedZeroInitialization.Yt.x(#AdvancedZeroInitialization.Yt.MakeYt(a#14#0#0, a#14#1#0))
     == a#14#0#0);

function AdvancedZeroInitialization.Yt.y(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#15#0#0: int, a#15#1#0: Box :: 
  { #AdvancedZeroInitialization.Yt.MakeYt(a#15#0#0, a#15#1#0) } 
  AdvancedZeroInitialization.Yt.y(#AdvancedZeroInitialization.Yt.MakeYt(a#15#0#0, a#15#1#0))
     == a#15#1#0);

// Inductive rank
axiom (forall a#16#0#0: int, a#16#1#0: Box :: 
  { #AdvancedZeroInitialization.Yt.MakeYt(a#16#0#0, a#16#1#0) } 
  BoxRank(a#16#1#0)
     < DtRank(#AdvancedZeroInitialization.Yt.MakeYt(a#16#0#0, a#16#1#0)));

// Depth-one case-split function
function $IsA#AdvancedZeroInitialization.Yt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#AdvancedZeroInitialization.Yt(d) } 
  $IsA#AdvancedZeroInitialization.Yt(d)
     ==> AdvancedZeroInitialization.Yt.MakeYt_q(d));

// Questionmark data type disjunctivity
axiom (forall AdvancedZeroInitialization.Yt$Y: Ty, d: DatatypeType :: 
  { AdvancedZeroInitialization.Yt.MakeYt_q(d), $Is(d, Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y)) } 
  $Is(d, Tclass.AdvancedZeroInitialization.Yt(AdvancedZeroInitialization.Yt$Y))
     ==> AdvancedZeroInitialization.Yt.MakeYt_q(d));

// Datatype extensional equality declaration
function AdvancedZeroInitialization.Yt#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #AdvancedZeroInitialization.Yt.MakeYt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { AdvancedZeroInitialization.Yt#Equal(a, b) } 
  true
     ==> (AdvancedZeroInitialization.Yt#Equal(a, b)
       <==> AdvancedZeroInitialization.Yt.x(a) == AdvancedZeroInitialization.Yt.x(b)
         && AdvancedZeroInitialization.Yt.y(a) == AdvancedZeroInitialization.Yt.y(b)));

// Datatype extensionality axiom: AdvancedZeroInitialization.Yt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { AdvancedZeroInitialization.Yt#Equal(a, b) } 
  AdvancedZeroInitialization.Yt#Equal(a, b) <==> a == b);

const unique class.AdvancedZeroInitialization.Yt: ClassName;

function Tclass.AdvancedZeroInitialization.Even() : Ty;

const unique Tagclass.AdvancedZeroInitialization.Even: TyTag;

// Tclass.AdvancedZeroInitialization.Even Tag
axiom Tag(Tclass.AdvancedZeroInitialization.Even())
     == Tagclass.AdvancedZeroInitialization.Even
   && TagFamily(Tclass.AdvancedZeroInitialization.Even()) == tytagFamily$Even;

// Box/unbox axiom for Tclass.AdvancedZeroInitialization.Even
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AdvancedZeroInitialization.Even()) } 
  $IsBox(bx, Tclass.AdvancedZeroInitialization.Even())
     ==> $Box($Unbox(bx): int) == bx
       && $Is($Unbox(bx): int, Tclass.AdvancedZeroInitialization.Even()));

// AdvancedZeroInitialization.Even: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass.AdvancedZeroInitialization.Even()) } 
  $Is(x#0, Tclass.AdvancedZeroInitialization.Even())
     <==> Mod(x#0, LitInt(2)) == LitInt(0));

// AdvancedZeroInitialization.Even: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass.AdvancedZeroInitialization.Even(), $h) } 
  $IsAlloc(x#0, Tclass.AdvancedZeroInitialization.Even(), $h));

const unique class.AdvancedZeroInitialization.__default: ClassName;

function Tclass.AdvancedZeroInitialization.__default() : Ty;

const unique Tagclass.AdvancedZeroInitialization.__default: TyTag;

// Tclass.AdvancedZeroInitialization.__default Tag
axiom Tag(Tclass.AdvancedZeroInitialization.__default())
     == Tagclass.AdvancedZeroInitialization.__default
   && TagFamily(Tclass.AdvancedZeroInitialization.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.AdvancedZeroInitialization.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.AdvancedZeroInitialization.__default()) } 
  $IsBox(bx, Tclass.AdvancedZeroInitialization.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.AdvancedZeroInitialization.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.AdvancedZeroInitialization.__default()) } 
  $Is($o, Tclass.AdvancedZeroInitialization.__default())
     <==> $o == null || dtype($o) == Tclass.AdvancedZeroInitialization.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.AdvancedZeroInitialization.__default(), $h) } 
  $IsAlloc($o, Tclass.AdvancedZeroInitialization.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$AdvancedZeroInitialization.__default.Test(which#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$AdvancedZeroInitialization.__default.Test(which#0: int);
  // user-defined preconditions
  requires which#0 == LitInt(0) || which#0 == LitInt(1);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for AdvancedZeroInitialization._default.PrCh
function AdvancedZeroInitialization.__default.PrCh(ch#0: char) : Seq Box;

function AdvancedZeroInitialization.__default.PrCh#canCall(ch#0: char) : bool;

// consequence axiom for AdvancedZeroInitialization.__default.PrCh
axiom true
   ==> (forall ch#0: char :: 
    { AdvancedZeroInitialization.__default.PrCh(ch#0) } 
    AdvancedZeroInitialization.__default.PrCh#canCall(ch#0) || $Is(ch#0, TChar)
       ==> $Is(AdvancedZeroInitialization.__default.PrCh(ch#0), TSeq(TChar)));

function AdvancedZeroInitialization.__default.PrCh#requires(char) : bool;

// #requires axiom for AdvancedZeroInitialization.__default.PrCh
axiom (forall ch#0: char :: 
  { AdvancedZeroInitialization.__default.PrCh#requires(ch#0) } 
  $Is(ch#0, TChar)
     ==> AdvancedZeroInitialization.__default.PrCh#requires(ch#0) == true);

// definition axiom for AdvancedZeroInitialization.__default.PrCh (revealed)
axiom true
   ==> (forall ch#0: char :: 
    { AdvancedZeroInitialization.__default.PrCh(ch#0) } 
    AdvancedZeroInitialization.__default.PrCh#canCall(ch#0) || $Is(ch#0, TChar)
       ==> AdvancedZeroInitialization.__default.PrCh(ch#0)
         == (if ch#0 == Lit(char#FromInt(0))
           then Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(39))), $Box(char#FromInt(92))), 
              $Box(char#FromInt(48))), 
            $Box(char#FromInt(39)))
           else (if ch#0 == Lit(char#FromInt(68))
             then Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(39))), $Box(char#FromInt(68))), 
              $Box(char#FromInt(39)))
             else Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(39))), $Box(char#FromInt(40))), 
                                    $Box(char#FromInt(111))), 
                                  $Box(char#FromInt(116))), 
                                $Box(char#FromInt(104))), 
                              $Box(char#FromInt(101))), 
                            $Box(char#FromInt(114))), 
                          $Box(char#FromInt(32))), 
                        $Box(char#FromInt(99))), 
                      $Box(char#FromInt(104))), 
                    $Box(char#FromInt(97))), 
                  $Box(char#FromInt(114))), 
                $Box(char#FromInt(41))), 
              $Box(char#FromInt(39))))));

// definition axiom for AdvancedZeroInitialization.__default.PrCh for all literals (revealed)
axiom true
   ==> (forall ch#0: char :: 
    {:weight 3} { AdvancedZeroInitialization.__default.PrCh(Lit(ch#0)) } 
    AdvancedZeroInitialization.__default.PrCh#canCall(Lit(ch#0)) || $Is(ch#0, TChar)
       ==> AdvancedZeroInitialization.__default.PrCh(Lit(ch#0))
         == (if Lit(ch#0) == Lit(char#FromInt(0))
           then Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(39))), $Box(char#FromInt(92))), 
              $Box(char#FromInt(48))), 
            $Box(char#FromInt(39)))
           else (if Lit(ch#0) == Lit(char#FromInt(68))
             then Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(39))), $Box(char#FromInt(68))), 
              $Box(char#FromInt(39)))
             else Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(39))), $Box(char#FromInt(40))), 
                                    $Box(char#FromInt(111))), 
                                  $Box(char#FromInt(116))), 
                                $Box(char#FromInt(104))), 
                              $Box(char#FromInt(101))), 
                            $Box(char#FromInt(114))), 
                          $Box(char#FromInt(32))), 
                        $Box(char#FromInt(99))), 
                      $Box(char#FromInt(104))), 
                    $Box(char#FromInt(97))), 
                  $Box(char#FromInt(114))), 
                $Box(char#FromInt(41))), 
              $Box(char#FromInt(39))))));

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

const unique tytagFamily$MyInt: TyTagFamily;

const unique tytagFamily$MyNewInt: TyTagFamily;

const unique tytagFamily$short: TyTagFamily;

const unique tytagFamily$short': TyTagFamily;

const unique tytagFamily$FavoriateReals: TyTagFamily;

const unique tytagFamily$NonEmptyIntSet: TyTagFamily;

const unique tytagFamily$WithTypeParameters: TyTagFamily;

const unique tytagFamily$Dt: TyTagFamily;

const unique tytagFamily$Tr: TyTagFamily;

const unique tytagFamily$MyClass: TyTagFamily;

const unique tytagFamily$MyClassWithCtor: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$Xt: TyTagFamily;

const unique tytagFamily$Yt: TyTagFamily;

const unique tytagFamily$Even: TyTagFamily;

const unique field$u: NameFamily;

const unique field$x: NameFamily;

const unique field$r: NameFamily;

const unique field$nes: NameFamily;

axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.MyClass?()) } 
  $o != null && $Is($o, Tclass._module.MyClass?())
     ==> $Is($o, Tclass._module.Tr()));

axiom (forall $o: ref, $heap: Heap :: 
  { $IsAlloc($o, Tclass._module.MyClass?(), $heap) } 
  $o != null && $IsAlloc($o, Tclass._module.MyClass?(), $heap)
     ==> $IsAlloc($o, Tclass._module.Tr(), $heap));

axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.MyClassWithCtor?()) } 
  $o != null && $Is($o, Tclass._module.MyClassWithCtor?())
     ==> $Is($o, Tclass._module.Tr()));

axiom (forall $o: ref, $heap: Heap :: 
  { $IsAlloc($o, Tclass._module.MyClassWithCtor?(), $heap) } 
  $o != null && $IsAlloc($o, Tclass._module.MyClassWithCtor?(), $heap)
     ==> $IsAlloc($o, Tclass._module.Tr(), $heap));
