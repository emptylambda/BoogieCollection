// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy -print:./NonZeroInitialization.bpl

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

const unique ##_System._tuple#2._#Make2: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#_System._tuple#2._#Make2(a#5#0#0, a#5#1#0))
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
     ==> (exists a#6#0#0: Box, a#6#1#0: Box :: 
      d == #_System._tuple#2._#Make2(a#6#0#0, a#6#1#0)));

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
axiom (forall _System._tuple#2$T0: Ty, _System._tuple#2$T1: Ty, a#7#0#0: Box, a#7#1#0: Box :: 
  { $Is(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1)) } 
  $Is(#_System._tuple#2._#Make2(a#7#0#0, a#7#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1))
     <==> $IsBox(a#7#0#0, _System._tuple#2$T0) && $IsBox(a#7#1#0, _System._tuple#2$T1));

// Constructor $IsAlloc
axiom (forall _System._tuple#2$T0: Ty, 
    _System._tuple#2$T1: Ty, 
    a#8#0#0: Box, 
    a#8#1#0: Box, 
    $h: Heap :: 
  { $IsAlloc(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0), 
      Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_System._tuple#2._#Make2(a#8#0#0, a#8#1#0), 
        Tclass._System.Tuple2(_System._tuple#2$T0, _System._tuple#2$T1), 
        $h)
       <==> $IsAllocBox(a#8#0#0, _System._tuple#2$T0, $h)
         && $IsAllocBox(a#8#1#0, _System._tuple#2$T1, $h)));

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
axiom (forall a#9#0#0: Box, a#9#1#0: Box :: 
  { #_System._tuple#2._#Make2(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #_System._tuple#2._#Make2(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_System._tuple#2._#Make2(a#9#0#0, a#9#1#0)));

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#10#0#0, a#10#1#0) } 
  _System.Tuple2._0(#_System._tuple#2._#Make2(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#_System._tuple#2._#Make2(a#11#0#0, a#11#1#0)));

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#12#0#0, a#12#1#0) } 
  _System.Tuple2._1(#_System._tuple#2._#Make2(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: Box :: 
  { #_System._tuple#2._#Make2(a#13#0#0, a#13#1#0) } 
  BoxRank(a#13#1#0) < DtRank(#_System._tuple#2._#Make2(a#13#0#0, a#13#1#0)));

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

procedure CheckWellformed$$_module.MyInt__Bad(x#0: int);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.MyInt__Bad(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type MyInt_Bad
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(4,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(6) <= x#0;
    }
    else
    {
        assume true;
        assert LitInt(6) <= LitInt(5);
    }
}



function Tclass._module.MyInt__Bad() : Ty;

const unique Tagclass._module.MyInt__Bad: TyTag;

// Tclass._module.MyInt__Bad Tag
axiom Tag(Tclass._module.MyInt__Bad()) == Tagclass._module.MyInt__Bad
   && TagFamily(Tclass._module.MyInt__Bad()) == tytagFamily$MyInt_Bad;

// Box/unbox axiom for Tclass._module.MyInt__Bad
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.MyInt__Bad()) } 
  $IsBox(bx, Tclass._module.MyInt__Bad())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.MyInt__Bad()));

// _module.MyInt_Bad: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.MyInt__Bad()) } 
  $Is(x#0, Tclass._module.MyInt__Bad()) <==> LitInt(6) <= x#0);

// _module.MyInt_Bad: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.MyInt__Bad(), $h) } 
  $IsAlloc(x#0, Tclass._module.MyInt__Bad(), $h));

procedure CheckWellformed$$_module.MyInt(x#0: int);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.MyInt(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type MyInt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(6,5): initial state"} true;
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
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.MyNewInt(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype MyNewInt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(8,8): initial state"} true;
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

procedure CheckWellformed$$_module.Six(x#0: int);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Six(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type Six
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(10,5): initial state"} true;
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



function Tclass._module.Six() : Ty;

const unique Tagclass._module.Six: TyTag;

// Tclass._module.Six Tag
axiom Tag(Tclass._module.Six()) == Tagclass._module.Six
   && TagFamily(Tclass._module.Six()) == tytagFamily$Six;

// Box/unbox axiom for Tclass._module.Six
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Six()) } 
  $IsBox(bx, Tclass._module.Six())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Six()));

// _module.Six: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.Six()) } 
  $Is(x#0, Tclass._module.Six()) <==> LitInt(6) <= x#0);

// _module.Six: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.Six(), $h) } 
  $IsAlloc(x#0, Tclass._module.Six(), $h));

procedure CheckWellformed$$_module.SixAgain(six#0: int where LitInt(6) <= six#0);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SixAgain(six#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;


    // AddWellformednessCheck for subset type SixAgain
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(11,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(4) <= six#0;
    }
    else
    {
        newtype$check#0 := LitInt(0);
        assert LitInt(6) <= newtype$check#0;
        assume true;
        assert LitInt(4) <= LitInt(0);
    }
}



function Tclass._module.SixAgain() : Ty;

const unique Tagclass._module.SixAgain: TyTag;

// Tclass._module.SixAgain Tag
axiom Tag(Tclass._module.SixAgain()) == Tagclass._module.SixAgain
   && TagFamily(Tclass._module.SixAgain()) == tytagFamily$SixAgain;

// Box/unbox axiom for Tclass._module.SixAgain
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SixAgain()) } 
  $IsBox(bx, Tclass._module.SixAgain())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.SixAgain()));

// _module.SixAgain: subset type $Is
axiom (forall six#0: int :: 
  { $Is(six#0, Tclass._module.SixAgain()) } 
  $Is(six#0, Tclass._module.SixAgain())
     <==> LitInt(6) <= six#0 && LitInt(4) <= six#0);

// _module.SixAgain: subset type $IsAlloc
axiom (forall six#0: int, $h: Heap :: 
  { $IsAlloc(six#0, Tclass._module.SixAgain(), $h) } 
  $IsAlloc(six#0, Tclass._module.SixAgain(), $h));

procedure CheckWellformed$$_module.SixAgainW(six#0: int where LitInt(6) <= six#0);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.SixAgainW(six#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;


    // AddWellformednessCheck for subset type SixAgainW
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(12,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(4) <= six#0;
    }
    else
    {
        newtype$check#0 := LitInt(4);
        assert LitInt(6) <= newtype$check#0;
        assume true;
        assert LitInt(4) <= LitInt(4);
    }
}



function Tclass._module.SixAgainW() : Ty;

const unique Tagclass._module.SixAgainW: TyTag;

// Tclass._module.SixAgainW Tag
axiom Tag(Tclass._module.SixAgainW()) == Tagclass._module.SixAgainW
   && TagFamily(Tclass._module.SixAgainW()) == tytagFamily$SixAgainW;

// Box/unbox axiom for Tclass._module.SixAgainW
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SixAgainW()) } 
  $IsBox(bx, Tclass._module.SixAgainW())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.SixAgainW()));

// _module.SixAgainW: subset type $Is
axiom (forall six#0: int :: 
  { $Is(six#0, Tclass._module.SixAgainW()) } 
  $Is(six#0, Tclass._module.SixAgainW())
     <==> LitInt(6) <= six#0 && LitInt(4) <= six#0);

// _module.SixAgainW: subset type $IsAlloc
axiom (forall six#0: int, $h: Heap :: 
  { $IsAlloc(six#0, Tclass._module.SixAgainW(), $h) } 
  $IsAlloc(six#0, Tclass._module.SixAgainW(), $h));

procedure CheckWellformed$$_module.Impossible(six#0: int where LitInt(6) <= six#0);
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Impossible(six#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;


    // AddWellformednessCheck for subset type Impossible
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(13,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume six#0 < 2;
    }
    else
    {
        newtype$check#0 := LitInt(0);
        assert LitInt(6) <= newtype$check#0;
        assume true;
        assert 0 < 2;
    }
}



function Tclass._module.Impossible() : Ty;

const unique Tagclass._module.Impossible: TyTag;

// Tclass._module.Impossible Tag
axiom Tag(Tclass._module.Impossible()) == Tagclass._module.Impossible
   && TagFamily(Tclass._module.Impossible()) == tytagFamily$Impossible;

// Box/unbox axiom for Tclass._module.Impossible
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Impossible()) } 
  $IsBox(bx, Tclass._module.Impossible())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Impossible()));

// _module.Impossible: subset type $Is
axiom (forall six#0: int :: 
  { $Is(six#0, Tclass._module.Impossible()) } 
  $Is(six#0, Tclass._module.Impossible()) <==> LitInt(6) <= six#0 && six#0 < 2);

// _module.Impossible: subset type $IsAlloc
axiom (forall six#0: int, $h: Heap :: 
  { $IsAlloc(six#0, Tclass._module.Impossible(), $h) } 
  $IsAlloc(six#0, Tclass._module.Impossible(), $h));

procedure CheckWellformed$$_module.NewSix(x#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NewSix(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype NewSix
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(15,8): initial state"} true;
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



function Tclass._module.NewSix() : Ty;

const unique Tagclass._module.NewSix: TyTag;

// Tclass._module.NewSix Tag
axiom Tag(Tclass._module.NewSix()) == Tagclass._module.NewSix
   && TagFamily(Tclass._module.NewSix()) == tytagFamily$NewSix;

// Box/unbox axiom for Tclass._module.NewSix
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NewSix()) } 
  $IsBox(bx, Tclass._module.NewSix())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.NewSix()));

// _module.NewSix: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.NewSix()) } 
  $Is(x#0, Tclass._module.NewSix()) <==> LitInt(6) <= x#0);

// _module.NewSix: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.NewSix(), $h) } 
  $IsAlloc(x#0, Tclass._module.NewSix(), $h));

const unique class._module.NewSix: ClassName;

procedure CheckWellformed$$_module.NewSixAgain(six#0: int where LitInt(6) <= six#0);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NewSixAgain(six#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;


    // AddWellformednessCheck for newtype NewSixAgain
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(16,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(4) <= six#0;
    }
    else
    {
        newtype$check#0 := LitInt(0);
        assert LitInt(6) <= newtype$check#0;
        assume true;
        assert LitInt(4) <= LitInt(0);
    }
}



function Tclass._module.NewSixAgain() : Ty;

const unique Tagclass._module.NewSixAgain: TyTag;

// Tclass._module.NewSixAgain Tag
axiom Tag(Tclass._module.NewSixAgain()) == Tagclass._module.NewSixAgain
   && TagFamily(Tclass._module.NewSixAgain()) == tytagFamily$NewSixAgain;

// Box/unbox axiom for Tclass._module.NewSixAgain
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NewSixAgain()) } 
  $IsBox(bx, Tclass._module.NewSixAgain())
     ==> $Box($Unbox(bx): int) == bx
       && $Is($Unbox(bx): int, Tclass._module.NewSixAgain()));

// _module.NewSixAgain: newtype $Is
axiom (forall six#0: int :: 
  { $Is(six#0, Tclass._module.NewSixAgain()) } 
  $Is(six#0, Tclass._module.NewSixAgain())
     <==> LitInt(6) <= six#0 && LitInt(4) <= six#0);

// _module.NewSixAgain: newtype $IsAlloc
axiom (forall six#0: int, $h: Heap :: 
  { $IsAlloc(six#0, Tclass._module.NewSixAgain(), $h) } 
  $IsAlloc(six#0, Tclass._module.NewSixAgain(), $h));

const unique class._module.NewSixAgain: ClassName;

procedure CheckWellformed$$_module.NewSixAgainW(six#0: int where LitInt(6) <= six#0);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NewSixAgainW(six#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;


    // AddWellformednessCheck for newtype NewSixAgainW
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(17,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(4) <= six#0;
    }
    else
    {
        newtype$check#0 := LitInt(4);
        assert LitInt(6) <= newtype$check#0;
        assume true;
        assert LitInt(4) <= LitInt(4);
    }
}



function Tclass._module.NewSixAgainW() : Ty;

const unique Tagclass._module.NewSixAgainW: TyTag;

// Tclass._module.NewSixAgainW Tag
axiom Tag(Tclass._module.NewSixAgainW()) == Tagclass._module.NewSixAgainW
   && TagFamily(Tclass._module.NewSixAgainW()) == tytagFamily$NewSixAgainW;

// Box/unbox axiom for Tclass._module.NewSixAgainW
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NewSixAgainW()) } 
  $IsBox(bx, Tclass._module.NewSixAgainW())
     ==> $Box($Unbox(bx): int) == bx
       && $Is($Unbox(bx): int, Tclass._module.NewSixAgainW()));

// _module.NewSixAgainW: newtype $Is
axiom (forall six#0: int :: 
  { $Is(six#0, Tclass._module.NewSixAgainW()) } 
  $Is(six#0, Tclass._module.NewSixAgainW())
     <==> LitInt(6) <= six#0 && LitInt(4) <= six#0);

// _module.NewSixAgainW: newtype $IsAlloc
axiom (forall six#0: int, $h: Heap :: 
  { $IsAlloc(six#0, Tclass._module.NewSixAgainW(), $h) } 
  $IsAlloc(six#0, Tclass._module.NewSixAgainW(), $h));

const unique class._module.NewSixAgainW: ClassName;

procedure CheckWellformed$$_module.NewSixAgainY(six#0: int where LitInt(6) <= six#0);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NewSixAgainY(six#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##six#0: int;
  var b$reqreads#0: bool;
  var newtype$check#0: int;

    b$reqreads#0 := true;

    // AddWellformednessCheck for newtype NewSixAgainY
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(18,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##six#0 := six#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##six#0, Tclass._module.NewSix(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Yes#canCall(six#0);
        assume _module.__default.Yes(six#0);
        assert b$reqreads#0;
    }
    else
    {
        newtype$check#0 := LitInt(4);
        assert LitInt(6) <= newtype$check#0;
        assume _module.__default.Yes#canCall(LitInt(4));
        assert {:subsumption 0} _module.__default.Yes#canCall(LitInt(4))
           ==> Lit(_module.__default.Yes(LitInt(4))) || LitInt(4) <= LitInt(4);
    }
}



function Tclass._module.NewSixAgainY() : Ty;

const unique Tagclass._module.NewSixAgainY: TyTag;

// Tclass._module.NewSixAgainY Tag
axiom Tag(Tclass._module.NewSixAgainY()) == Tagclass._module.NewSixAgainY
   && TagFamily(Tclass._module.NewSixAgainY()) == tytagFamily$NewSixAgainY;

// Box/unbox axiom for Tclass._module.NewSixAgainY
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NewSixAgainY()) } 
  $IsBox(bx, Tclass._module.NewSixAgainY())
     ==> $Box($Unbox(bx): int) == bx
       && $Is($Unbox(bx): int, Tclass._module.NewSixAgainY()));

// _module.NewSixAgainY: newtype $Is
axiom (forall six#0: int :: 
  { $Is(six#0, Tclass._module.NewSixAgainY()) } 
  $Is(six#0, Tclass._module.NewSixAgainY())
     <==> LitInt(6) <= six#0 && _module.__default.Yes(six#0));

// _module.NewSixAgainY: newtype $IsAlloc
axiom (forall six#0: int, $h: Heap :: 
  { $IsAlloc(six#0, Tclass._module.NewSixAgainY(), $h) } 
  $IsAlloc(six#0, Tclass._module.NewSixAgainY(), $h));

const unique class._module.NewSixAgainY: ClassName;

procedure CheckWellformed$$_module.NewImpossible(six#0: int where LitInt(6) <= six#0);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NewImpossible(six#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var newtype$check#1: int;


    // AddWellformednessCheck for newtype NewImpossible
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(19,8): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        newtype$check#0 := LitInt(6);
        assert LitInt(6) <= newtype$check#0;
        assume six#0 < 6;
    }
    else
    {
        newtype$check#1 := LitInt(0);
        assert LitInt(6) <= newtype$check#1;
        assume true;
        assert 0 < 6;
    }
}



function Tclass._module.NewImpossible() : Ty;

const unique Tagclass._module.NewImpossible: TyTag;

// Tclass._module.NewImpossible Tag
axiom Tag(Tclass._module.NewImpossible()) == Tagclass._module.NewImpossible
   && TagFamily(Tclass._module.NewImpossible()) == tytagFamily$NewImpossible;

// Box/unbox axiom for Tclass._module.NewImpossible
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.NewImpossible()) } 
  $IsBox(bx, Tclass._module.NewImpossible())
     ==> $Box($Unbox(bx): int) == bx
       && $Is($Unbox(bx): int, Tclass._module.NewImpossible()));

// _module.NewImpossible: newtype $Is
axiom (forall six#0: int :: 
  { $Is(six#0, Tclass._module.NewImpossible()) } 
  $Is(six#0, Tclass._module.NewImpossible()) <==> LitInt(6) <= six#0 && six#0 < 6);

// _module.NewImpossible: newtype $IsAlloc
axiom (forall six#0: int, $h: Heap :: 
  { $IsAlloc(six#0, Tclass._module.NewImpossible(), $h) } 
  $IsAlloc(six#0, Tclass._module.NewImpossible(), $h));

const unique class._module.NewImpossible: ClassName;

const unique class._module.YetAnotherNewSix: ClassName;

// Constructor function declaration
function #_module.List.Nil() : DatatypeType;

const unique ##_module.List.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.List.Nil()) == ##_module.List.Nil;

function _module.List.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.Nil_q(d) } 
  _module.List.Nil_q(d) <==> DatatypeCtorId(d) == ##_module.List.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.Nil_q(d) } 
  _module.List.Nil_q(d) ==> d == #_module.List.Nil());

function Tclass._module.List(Ty) : Ty;

const unique Tagclass._module.List: TyTag;

// Tclass._module.List Tag
axiom (forall _module.List$G: Ty :: 
  { Tclass._module.List(_module.List$G) } 
  Tag(Tclass._module.List(_module.List$G)) == Tagclass._module.List
     && TagFamily(Tclass._module.List(_module.List$G)) == tytagFamily$List);

// Tclass._module.List injectivity 0
axiom (forall _module.List$G: Ty :: 
  { Tclass._module.List(_module.List$G) } 
  Tclass._module.List_0(Tclass._module.List(_module.List$G)) == _module.List$G);

function Tclass._module.List_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.List
axiom (forall _module.List$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.List(_module.List$G)) } 
  $IsBox(bx, Tclass._module.List(_module.List$G))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.List(_module.List$G)));

// Constructor $Is
axiom (forall _module.List$G: Ty :: 
  { $Is(#_module.List.Nil(), Tclass._module.List(_module.List$G)) } 
  $Is(#_module.List.Nil(), Tclass._module.List(_module.List$G)));

// Constructor $IsAlloc
axiom (forall _module.List$G: Ty, $h: Heap :: 
  { $IsAlloc(#_module.List.Nil(), Tclass._module.List(_module.List$G), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.List.Nil(), Tclass._module.List(_module.List$G), $h));

// Constructor literal
axiom #_module.List.Nil() == Lit(#_module.List.Nil());

// Constructor function declaration
function #_module.List.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: DatatypeType :: 
  { #_module.List.Cons(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#_module.List.Cons(a#5#0#0, a#5#1#0)) == ##_module.List.Cons);

function _module.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.Cons_q(d) } 
  _module.List.Cons_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: DatatypeType :: 
      d == #_module.List.Cons(a#6#0#0, a#6#1#0)));

// Constructor $Is
axiom (forall _module.List$G: Ty, a#7#0#0: Box, a#7#1#0: DatatypeType :: 
  { $Is(#_module.List.Cons(a#7#0#0, a#7#1#0), Tclass._module.List(_module.List$G)) } 
  $Is(#_module.List.Cons(a#7#0#0, a#7#1#0), Tclass._module.List(_module.List$G))
     <==> $IsBox(a#7#0#0, _module.List$G)
       && $Is(a#7#1#0, Tclass._module.List(_module.List$G)));

// Constructor $IsAlloc
axiom (forall _module.List$G: Ty, a#8#0#0: Box, a#8#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.List.Cons(a#8#0#0, a#8#1#0), Tclass._module.List(_module.List$G), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.List.Cons(a#8#0#0, a#8#1#0), Tclass._module.List(_module.List$G), $h)
       <==> $IsAllocBox(a#8#0#0, _module.List$G, $h)
         && $IsAlloc(a#8#1#0, Tclass._module.List(_module.List$G), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$G: Ty, $h: Heap :: 
  { $IsAllocBox(_module.List._h0(d), _module.List$G, $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$G), $h)
     ==> $IsAllocBox(_module.List._h0(d), _module.List$G, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$G: Ty, $h: Heap :: 
  { $IsAlloc(_module.List._h1(d), Tclass._module.List(_module.List$G), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$G), $h)
     ==> $IsAlloc(_module.List._h1(d), Tclass._module.List(_module.List$G), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType :: 
  { #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_module.List.Cons(a#9#0#0, a#9#1#0)));

function _module.List._h0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType :: 
  { #_module.List.Cons(a#10#0#0, a#10#1#0) } 
  _module.List._h0(#_module.List.Cons(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType :: 
  { #_module.List.Cons(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#_module.List.Cons(a#11#0#0, a#11#1#0)));

function _module.List._h1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType :: 
  { #_module.List.Cons(a#12#0#0, a#12#1#0) } 
  _module.List._h1(#_module.List.Cons(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: DatatypeType :: 
  { #_module.List.Cons(a#13#0#0, a#13#1#0) } 
  DtRank(a#13#1#0) < DtRank(#_module.List.Cons(a#13#0#0, a#13#1#0)));

// Depth-one case-split function
function $IsA#_module.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.List(d) } 
  $IsA#_module.List(d) ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.List$G: Ty, d: DatatypeType :: 
  { _module.List.Cons_q(d), $Is(d, Tclass._module.List(_module.List$G)) } 
    { _module.List.Nil_q(d), $Is(d, Tclass._module.List(_module.List$G)) } 
  $Is(d, Tclass._module.List(_module.List$G))
     ==> _module.List.Nil_q(d) || _module.List.Cons_q(d));

// Datatype extensional equality declaration
function _module.List#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.List.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b), _module.List.Nil_q(a) } 
    { _module.List#Equal(a, b), _module.List.Nil_q(b) } 
  _module.List.Nil_q(a) && _module.List.Nil_q(b)
     ==> (_module.List#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.List.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b), _module.List.Cons_q(a) } 
    { _module.List#Equal(a, b), _module.List.Cons_q(b) } 
  _module.List.Cons_q(a) && _module.List.Cons_q(b)
     ==> (_module.List#Equal(a, b)
       <==> _module.List._h0(a) == _module.List._h0(b)
         && _module.List#Equal(_module.List._h1(a), _module.List._h1(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

procedure CheckWellformed$$_module.ListTwo(_module.ListTwo$G: Ty, 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.List(TSet(_module.ListTwo$G))));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ListTwo(_module.ListTwo$G: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type ListTwo
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(36,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##xs#0 := xs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#0, Tclass._module.List(TSet(_module.ListTwo$G)), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Length#canCall(TSet(_module.ListTwo$G), xs#0);
        assume LitInt(2) <= _module.__default.Length(TSet(_module.ListTwo$G), $LS($LZ), xs#0);
        assert b$reqreads#0;
    }
    else
    {
        assume _module.__default.Length#canCall(TSet(_module.ListTwo$G), 
          Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
              Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil()))))));
        assert {:subsumption 0} LitInt(2)
           <= LitInt(_module.__default.Length(TSet(_module.ListTwo$G), 
              $LS($LS($LZ)), 
              Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                  Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil())))))));
    }
}



function Tclass._module.ListTwo(Ty) : Ty;

const unique Tagclass._module.ListTwo: TyTag;

// Tclass._module.ListTwo Tag
axiom (forall _module.ListTwo$G: Ty :: 
  { Tclass._module.ListTwo(_module.ListTwo$G) } 
  Tag(Tclass._module.ListTwo(_module.ListTwo$G)) == Tagclass._module.ListTwo
     && TagFamily(Tclass._module.ListTwo(_module.ListTwo$G)) == tytagFamily$ListTwo);

// Tclass._module.ListTwo injectivity 0
axiom (forall _module.ListTwo$G: Ty :: 
  { Tclass._module.ListTwo(_module.ListTwo$G) } 
  Tclass._module.ListTwo_0(Tclass._module.ListTwo(_module.ListTwo$G))
     == _module.ListTwo$G);

function Tclass._module.ListTwo_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.ListTwo
axiom (forall _module.ListTwo$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.ListTwo(_module.ListTwo$G)) } 
  $IsBox(bx, Tclass._module.ListTwo(_module.ListTwo$G))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.ListTwo(_module.ListTwo$G)));

// _module.ListTwo: subset type $Is
axiom (forall _module.ListTwo$G: Ty, xs#0: DatatypeType :: 
  { $Is(xs#0, Tclass._module.ListTwo(_module.ListTwo$G)) } 
  $Is(xs#0, Tclass._module.ListTwo(_module.ListTwo$G))
     <==> $Is(xs#0, Tclass._module.List(TSet(_module.ListTwo$G)))
       && LitInt(2) <= _module.__default.Length(TSet(_module.ListTwo$G), $LS($LZ), xs#0));

// _module.ListTwo: subset type $IsAlloc
axiom (forall _module.ListTwo$G: Ty, xs#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(xs#0, Tclass._module.ListTwo(_module.ListTwo$G), $h) } 
  $IsAlloc(xs#0, Tclass._module.ListTwo(_module.ListTwo$G), $h)
     <==> $IsAlloc(xs#0, Tclass._module.List(TSet(_module.ListTwo$G)), $h));

procedure CheckWellformed$$_module.TwoAgain(_module.TwoAgain$G: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, 
        Tclass._module.ListTwo(Tclass._System.Tuple2(TSet(_module.TwoAgain$G), Tclass._System.Tuple0()))));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.TwoAgain(_module.TwoAgain$G: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type TwoAgain
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(37,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##xs#0 := xs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#0, 
          Tclass._module.List(TSet(Tclass._System.Tuple2(TSet(_module.TwoAgain$G), Tclass._System.Tuple0()))), 
          $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Length#canCall(TSet(Tclass._System.Tuple2(TSet(_module.TwoAgain$G), Tclass._System.Tuple0())), 
          xs#0);
        assume LitInt(1)
           <= _module.__default.Length(TSet(Tclass._System.Tuple2(TSet(_module.TwoAgain$G), Tclass._System.Tuple0())), 
            $LS($LZ), 
            xs#0);
        assert b$reqreads#0;
    }
    else
    {
        assert false;
    }
}



function Tclass._module.TwoAgain(Ty) : Ty;

const unique Tagclass._module.TwoAgain: TyTag;

// Tclass._module.TwoAgain Tag
axiom (forall _module.TwoAgain$G: Ty :: 
  { Tclass._module.TwoAgain(_module.TwoAgain$G) } 
  Tag(Tclass._module.TwoAgain(_module.TwoAgain$G)) == Tagclass._module.TwoAgain
     && TagFamily(Tclass._module.TwoAgain(_module.TwoAgain$G)) == tytagFamily$TwoAgain);

// Tclass._module.TwoAgain injectivity 0
axiom (forall _module.TwoAgain$G: Ty :: 
  { Tclass._module.TwoAgain(_module.TwoAgain$G) } 
  Tclass._module.TwoAgain_0(Tclass._module.TwoAgain(_module.TwoAgain$G))
     == _module.TwoAgain$G);

function Tclass._module.TwoAgain_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.TwoAgain
axiom (forall _module.TwoAgain$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.TwoAgain(_module.TwoAgain$G)) } 
  $IsBox(bx, Tclass._module.TwoAgain(_module.TwoAgain$G))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.TwoAgain(_module.TwoAgain$G)));

// _module.TwoAgain: subset type $Is
axiom (forall _module.TwoAgain$G: Ty, xs#0: DatatypeType :: 
  { $Is(xs#0, Tclass._module.TwoAgain(_module.TwoAgain$G)) } 
  $Is(xs#0, Tclass._module.TwoAgain(_module.TwoAgain$G))
     <==> $Is(xs#0, 
        Tclass._module.ListTwo(Tclass._System.Tuple2(TSet(_module.TwoAgain$G), Tclass._System.Tuple0())))
       && LitInt(1)
         <= _module.__default.Length(TSet(Tclass._System.Tuple2(TSet(_module.TwoAgain$G), Tclass._System.Tuple0())), 
          $LS($LZ), 
          xs#0));

// _module.TwoAgain: subset type $IsAlloc
axiom (forall _module.TwoAgain$G: Ty, xs#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(xs#0, Tclass._module.TwoAgain(_module.TwoAgain$G), $h) } 
  $IsAlloc(xs#0, Tclass._module.TwoAgain(_module.TwoAgain$G), $h)
     <==> $IsAlloc(xs#0, 
      Tclass._module.ListTwo(Tclass._System.Tuple2(TSet(_module.TwoAgain$G), Tclass._System.Tuple0())), 
      $h));

procedure CheckWellformed$$_module.TwoAgainW(_module.TwoAgainW$G: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.ListTwo(TSet(_module.TwoAgainW$G))));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.TwoAgainW(_module.TwoAgainW$G: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;
  var newtype$check#0: DatatypeType;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type TwoAgainW
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(38,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##xs#0 := xs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#0, Tclass._module.List(TSet(TSet(_module.TwoAgainW$G))), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Length#canCall(TSet(TSet(_module.TwoAgainW$G)), xs#0);
        assume LitInt(1)
           <= _module.__default.Length(TSet(TSet(_module.TwoAgainW$G)), $LS($LZ), xs#0);
        assert b$reqreads#0;
    }
    else
    {
        newtype$check#0 := Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil())));
        assert LitInt(2)
           <= _module.__default.Length(TSet(TSet(_module.TwoAgainW$G)), $LS($LZ), newtype$check#0);
        assume _module.__default.Length#canCall(TSet(TSet(_module.TwoAgainW$G)), 
          Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil()))));
        assert {:subsumption 0} LitInt(1)
           <= LitInt(_module.__default.Length(TSet(TSet(_module.TwoAgainW$G)), 
              $LS($LS($LZ)), 
              Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil())))));
    }
}



function Tclass._module.TwoAgainW(Ty) : Ty;

const unique Tagclass._module.TwoAgainW: TyTag;

// Tclass._module.TwoAgainW Tag
axiom (forall _module.TwoAgainW$G: Ty :: 
  { Tclass._module.TwoAgainW(_module.TwoAgainW$G) } 
  Tag(Tclass._module.TwoAgainW(_module.TwoAgainW$G)) == Tagclass._module.TwoAgainW
     && TagFamily(Tclass._module.TwoAgainW(_module.TwoAgainW$G))
       == tytagFamily$TwoAgainW);

// Tclass._module.TwoAgainW injectivity 0
axiom (forall _module.TwoAgainW$G: Ty :: 
  { Tclass._module.TwoAgainW(_module.TwoAgainW$G) } 
  Tclass._module.TwoAgainW_0(Tclass._module.TwoAgainW(_module.TwoAgainW$G))
     == _module.TwoAgainW$G);

function Tclass._module.TwoAgainW_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.TwoAgainW
axiom (forall _module.TwoAgainW$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.TwoAgainW(_module.TwoAgainW$G)) } 
  $IsBox(bx, Tclass._module.TwoAgainW(_module.TwoAgainW$G))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.TwoAgainW(_module.TwoAgainW$G)));

// _module.TwoAgainW: subset type $Is
axiom (forall _module.TwoAgainW$G: Ty, xs#0: DatatypeType :: 
  { $Is(xs#0, Tclass._module.TwoAgainW(_module.TwoAgainW$G)) } 
  $Is(xs#0, Tclass._module.TwoAgainW(_module.TwoAgainW$G))
     <==> $Is(xs#0, Tclass._module.ListTwo(TSet(_module.TwoAgainW$G)))
       && LitInt(1)
         <= _module.__default.Length(TSet(TSet(_module.TwoAgainW$G)), $LS($LZ), xs#0));

// _module.TwoAgainW: subset type $IsAlloc
axiom (forall _module.TwoAgainW$G: Ty, xs#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(xs#0, Tclass._module.TwoAgainW(_module.TwoAgainW$G), $h) } 
  $IsAlloc(xs#0, Tclass._module.TwoAgainW(_module.TwoAgainW$G), $h)
     <==> $IsAlloc(xs#0, Tclass._module.ListTwo(TSet(_module.TwoAgainW$G)), $h));

procedure CheckWellformed$$_module.TwoImpossible(_module.TwoImpossible$G: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.ListTwo(TSet(_module.TwoImpossible$G))));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.TwoImpossible(_module.TwoImpossible$G: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type TwoImpossible
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(39,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##xs#0 := xs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#0, Tclass._module.List(TSet(TSet(_module.TwoImpossible$G))), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Length#canCall(TSet(TSet(_module.TwoImpossible$G)), xs#0);
        assume _module.__default.Length(TSet(TSet(_module.TwoImpossible$G)), $LS($LZ), xs#0)
           < 2;
        assert b$reqreads#0;
    }
    else
    {
        assert false;
    }
}



function Tclass._module.TwoImpossible(Ty) : Ty;

const unique Tagclass._module.TwoImpossible: TyTag;

// Tclass._module.TwoImpossible Tag
axiom (forall _module.TwoImpossible$G: Ty :: 
  { Tclass._module.TwoImpossible(_module.TwoImpossible$G) } 
  Tag(Tclass._module.TwoImpossible(_module.TwoImpossible$G))
       == Tagclass._module.TwoImpossible
     && TagFamily(Tclass._module.TwoImpossible(_module.TwoImpossible$G))
       == tytagFamily$TwoImpossible);

// Tclass._module.TwoImpossible injectivity 0
axiom (forall _module.TwoImpossible$G: Ty :: 
  { Tclass._module.TwoImpossible(_module.TwoImpossible$G) } 
  Tclass._module.TwoImpossible_0(Tclass._module.TwoImpossible(_module.TwoImpossible$G))
     == _module.TwoImpossible$G);

function Tclass._module.TwoImpossible_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.TwoImpossible
axiom (forall _module.TwoImpossible$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.TwoImpossible(_module.TwoImpossible$G)) } 
  $IsBox(bx, Tclass._module.TwoImpossible(_module.TwoImpossible$G))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.TwoImpossible(_module.TwoImpossible$G)));

// _module.TwoImpossible: subset type $Is
axiom (forall _module.TwoImpossible$G: Ty, xs#0: DatatypeType :: 
  { $Is(xs#0, Tclass._module.TwoImpossible(_module.TwoImpossible$G)) } 
  $Is(xs#0, Tclass._module.TwoImpossible(_module.TwoImpossible$G))
     <==> $Is(xs#0, Tclass._module.ListTwo(TSet(_module.TwoImpossible$G)))
       && _module.__default.Length(TSet(TSet(_module.TwoImpossible$G)), $LS($LZ), xs#0)
         < 2);

// _module.TwoImpossible: subset type $IsAlloc
axiom (forall _module.TwoImpossible$G: Ty, xs#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(xs#0, Tclass._module.TwoImpossible(_module.TwoImpossible$G), $h) } 
  $IsAlloc(xs#0, Tclass._module.TwoImpossible(_module.TwoImpossible$G), $h)
     <==> $IsAlloc(xs#0, Tclass._module.ListTwo(TSet(_module.TwoImpossible$G)), $h));

procedure CheckWellformed$$_module.ListFour(_module.ListFour$G: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(TSet(_module.ListFour$G))));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ListFour(_module.ListFour$G: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type ListFour
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(42,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##xs#0 := xs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#0, Tclass._module.List(TSet(_module.ListFour$G)), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Length#canCall(TSet(_module.ListFour$G), xs#0);
        assume LitInt(4) <= _module.__default.Length(TSet(_module.ListFour$G), $LS($LZ), xs#0);
        assert b$reqreads#0;
    }
    else
    {
        assume _module.__default.Length#canCall(TSet(_module.ListFour$G), 
          Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
              Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                  Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                      Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil()))))))))));
        assert {:subsumption 0} LitInt(4)
           <= LitInt(_module.__default.Length(TSet(_module.ListFour$G), 
              $LS($LS($LZ)), 
              Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                  Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                      Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                          Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil())))))))))));
    }
}



function Tclass._module.ListFour(Ty) : Ty;

const unique Tagclass._module.ListFour: TyTag;

// Tclass._module.ListFour Tag
axiom (forall _module.ListFour$G: Ty :: 
  { Tclass._module.ListFour(_module.ListFour$G) } 
  Tag(Tclass._module.ListFour(_module.ListFour$G)) == Tagclass._module.ListFour
     && TagFamily(Tclass._module.ListFour(_module.ListFour$G)) == tytagFamily$ListFour);

// Tclass._module.ListFour injectivity 0
axiom (forall _module.ListFour$G: Ty :: 
  { Tclass._module.ListFour(_module.ListFour$G) } 
  Tclass._module.ListFour_0(Tclass._module.ListFour(_module.ListFour$G))
     == _module.ListFour$G);

function Tclass._module.ListFour_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.ListFour
axiom (forall _module.ListFour$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.ListFour(_module.ListFour$G)) } 
  $IsBox(bx, Tclass._module.ListFour(_module.ListFour$G))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.ListFour(_module.ListFour$G)));

// _module.ListFour: subset type $Is
axiom (forall _module.ListFour$G: Ty, xs#0: DatatypeType :: 
  { $Is(xs#0, Tclass._module.ListFour(_module.ListFour$G)) } 
  $Is(xs#0, Tclass._module.ListFour(_module.ListFour$G))
     <==> $Is(xs#0, Tclass._module.List(TSet(_module.ListFour$G)))
       && LitInt(4) <= _module.__default.Length(TSet(_module.ListFour$G), $LS($LZ), xs#0));

// _module.ListFour: subset type $IsAlloc
axiom (forall _module.ListFour$G: Ty, xs#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(xs#0, Tclass._module.ListFour(_module.ListFour$G), $h) } 
  $IsAlloc(xs#0, Tclass._module.ListFour(_module.ListFour$G), $h)
     <==> $IsAlloc(xs#0, Tclass._module.List(TSet(_module.ListFour$G)), $h));

procedure CheckWellformed$$_module.ListFour_k(_module.ListFour'$G: Ty, 
    xs#0: DatatypeType where $Is(xs#0, Tclass._module.ListTwo(_module.ListFour'$G)));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.ListFour_k(_module.ListFour'$G: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;
  var newtype$check#0: DatatypeType;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type ListFour'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(43,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##xs#0 := xs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#0, Tclass._module.List(TSet(_module.ListFour'$G)), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Length#canCall(TSet(_module.ListFour'$G), xs#0);
        assume LitInt(4) <= _module.__default.Length(TSet(_module.ListFour'$G), $LS($LZ), xs#0);
        assert b$reqreads#0;
    }
    else
    {
        newtype$check#0 := Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
            Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                    Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil())))))))));
        assert LitInt(2)
           <= _module.__default.Length(TSet(_module.ListFour'$G), $LS($LZ), newtype$check#0);
        assume _module.__default.Length#canCall(TSet(_module.ListFour'$G), 
          Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
              Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                  Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                      Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil()))))))))));
        assert {:subsumption 0} LitInt(4)
           <= LitInt(_module.__default.Length(TSet(_module.ListFour'$G), 
              $LS($LS($LZ)), 
              Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                  Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                      Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), 
                          Lit(#_module.List.Cons($Box(Lit(Set#Empty(): Set Box)), Lit(#_module.List.Nil())))))))))));
    }
}



function Tclass._module.ListFour_k(Ty) : Ty;

const unique Tagclass._module.ListFour_k: TyTag;

// Tclass._module.ListFour_k Tag
axiom (forall _module.ListFour'$G: Ty :: 
  { Tclass._module.ListFour_k(_module.ListFour'$G) } 
  Tag(Tclass._module.ListFour_k(_module.ListFour'$G))
       == Tagclass._module.ListFour_k
     && TagFamily(Tclass._module.ListFour_k(_module.ListFour'$G))
       == tytagFamily$ListFour');

// Tclass._module.ListFour_k injectivity 0
axiom (forall _module.ListFour'$G: Ty :: 
  { Tclass._module.ListFour_k(_module.ListFour'$G) } 
  Tclass._module.ListFour_k_0(Tclass._module.ListFour_k(_module.ListFour'$G))
     == _module.ListFour'$G);

function Tclass._module.ListFour_k_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.ListFour_k
axiom (forall _module.ListFour'$G: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.ListFour_k(_module.ListFour'$G)) } 
  $IsBox(bx, Tclass._module.ListFour_k(_module.ListFour'$G))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.ListFour_k(_module.ListFour'$G)));

// _module.ListFour': subset type $Is
axiom (forall _module.ListFour'$G: Ty, xs#0: DatatypeType :: 
  { $Is(xs#0, Tclass._module.ListFour_k(_module.ListFour'$G)) } 
  $Is(xs#0, Tclass._module.ListFour_k(_module.ListFour'$G))
     <==> $Is(xs#0, Tclass._module.ListTwo(_module.ListFour'$G))
       && LitInt(4) <= _module.__default.Length(TSet(_module.ListFour'$G), $LS($LZ), xs#0));

// _module.ListFour': subset type $IsAlloc
axiom (forall _module.ListFour'$G: Ty, xs#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(xs#0, Tclass._module.ListFour_k(_module.ListFour'$G), $h) } 
  $IsAlloc(xs#0, Tclass._module.ListFour_k(_module.ListFour'$G), $h)
     <==> $IsAlloc(xs#0, Tclass._module.ListTwo(_module.ListFour'$G), $h));

// Constructor function declaration
function #_module.Yt.MakeYt(int, Box) : DatatypeType;

const unique ##_module.Yt.MakeYt: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: int, a#0#1#0: Box :: 
  { #_module.Yt.MakeYt(a#0#0#0, a#0#1#0) } 
  DatatypeCtorId(#_module.Yt.MakeYt(a#0#0#0, a#0#1#0)) == ##_module.Yt.MakeYt);

function _module.Yt.MakeYt_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Yt.MakeYt_q(d) } 
  _module.Yt.MakeYt_q(d) <==> DatatypeCtorId(d) == ##_module.Yt.MakeYt);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Yt.MakeYt_q(d) } 
  _module.Yt.MakeYt_q(d)
     ==> (exists a#1#0#0: int, a#1#1#0: Box :: d == #_module.Yt.MakeYt(a#1#0#0, a#1#1#0)));

function Tclass._module.Yt(Ty) : Ty;

const unique Tagclass._module.Yt: TyTag;

// Tclass._module.Yt Tag
axiom (forall _module.Yt$Y: Ty :: 
  { Tclass._module.Yt(_module.Yt$Y) } 
  Tag(Tclass._module.Yt(_module.Yt$Y)) == Tagclass._module.Yt
     && TagFamily(Tclass._module.Yt(_module.Yt$Y)) == tytagFamily$Yt);

// Tclass._module.Yt injectivity 0
axiom (forall _module.Yt$Y: Ty :: 
  { Tclass._module.Yt(_module.Yt$Y) } 
  Tclass._module.Yt_0(Tclass._module.Yt(_module.Yt$Y)) == _module.Yt$Y);

function Tclass._module.Yt_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Yt
axiom (forall _module.Yt$Y: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Yt(_module.Yt$Y)) } 
  $IsBox(bx, Tclass._module.Yt(_module.Yt$Y))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Yt(_module.Yt$Y)));

// Constructor $Is
axiom (forall _module.Yt$Y: Ty, a#2#0#0: int, a#2#1#0: Box :: 
  { $Is(#_module.Yt.MakeYt(a#2#0#0, a#2#1#0), Tclass._module.Yt(_module.Yt$Y)) } 
  $Is(#_module.Yt.MakeYt(a#2#0#0, a#2#1#0), Tclass._module.Yt(_module.Yt$Y))
     <==> $Is(a#2#0#0, TInt) && $IsBox(a#2#1#0, _module.Yt$Y));

// Constructor $IsAlloc
axiom (forall _module.Yt$Y: Ty, a#3#0#0: int, a#3#1#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Yt.MakeYt(a#3#0#0, a#3#1#0), Tclass._module.Yt(_module.Yt$Y), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Yt.MakeYt(a#3#0#0, a#3#1#0), Tclass._module.Yt(_module.Yt$Y), $h)
       <==> $IsAlloc(a#3#0#0, TInt, $h) && $IsAllocBox(a#3#1#0, _module.Yt$Y, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Yt.x(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Yt.MakeYt_q(d)
       && (exists _module.Yt$Y: Ty :: 
        { $IsAlloc(d, Tclass._module.Yt(_module.Yt$Y), $h) } 
        $IsAlloc(d, Tclass._module.Yt(_module.Yt$Y), $h))
     ==> $IsAlloc(_module.Yt.x(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Yt$Y: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Yt.y(d), _module.Yt$Y, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Yt.MakeYt_q(d)
       && $IsAlloc(d, Tclass._module.Yt(_module.Yt$Y), $h)
     ==> $IsAllocBox(_module.Yt.y(d), _module.Yt$Y, $h));

// Constructor literal
axiom (forall a#4#0#0: int, a#4#1#0: Box :: 
  { #_module.Yt.MakeYt(LitInt(a#4#0#0), Lit(a#4#1#0)) } 
  #_module.Yt.MakeYt(LitInt(a#4#0#0), Lit(a#4#1#0))
     == Lit(#_module.Yt.MakeYt(a#4#0#0, a#4#1#0)));

function _module.Yt.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#5#0#0: int, a#5#1#0: Box :: 
  { #_module.Yt.MakeYt(a#5#0#0, a#5#1#0) } 
  _module.Yt.x(#_module.Yt.MakeYt(a#5#0#0, a#5#1#0)) == a#5#0#0);

function _module.Yt.y(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#6#0#0: int, a#6#1#0: Box :: 
  { #_module.Yt.MakeYt(a#6#0#0, a#6#1#0) } 
  _module.Yt.y(#_module.Yt.MakeYt(a#6#0#0, a#6#1#0)) == a#6#1#0);

// Inductive rank
axiom (forall a#7#0#0: int, a#7#1#0: Box :: 
  { #_module.Yt.MakeYt(a#7#0#0, a#7#1#0) } 
  BoxRank(a#7#1#0) < DtRank(#_module.Yt.MakeYt(a#7#0#0, a#7#1#0)));

// Depth-one case-split function
function $IsA#_module.Yt(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Yt(d) } 
  $IsA#_module.Yt(d) ==> _module.Yt.MakeYt_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Yt$Y: Ty, d: DatatypeType :: 
  { _module.Yt.MakeYt_q(d), $Is(d, Tclass._module.Yt(_module.Yt$Y)) } 
  $Is(d, Tclass._module.Yt(_module.Yt$Y)) ==> _module.Yt.MakeYt_q(d));

// Datatype extensional equality declaration
function _module.Yt#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Yt.MakeYt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Yt#Equal(a, b) } 
  true
     ==> (_module.Yt#Equal(a, b)
       <==> _module.Yt.x(a) == _module.Yt.x(b) && _module.Yt.y(a) == _module.Yt.y(b)));

// Datatype extensionality axiom: _module.Yt
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Yt#Equal(a, b) } 
  _module.Yt#Equal(a, b) <==> a == b);

const unique class._module.Yt: ClassName;

procedure CheckWellformed$$_module.Even(x#0: int);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Even(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type Even
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(48,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assert LitInt(2) != 0;
        assume Mod(x#0, LitInt(2)) == LitInt(0);
    }
    else
    {
        assume true;
        assert LitInt(Mod(0, LitInt(2))) == LitInt(0);
    }
}



function Tclass._module.Even() : Ty;

const unique Tagclass._module.Even: TyTag;

// Tclass._module.Even Tag
axiom Tag(Tclass._module.Even()) == Tagclass._module.Even
   && TagFamily(Tclass._module.Even()) == tytagFamily$Even;

// Box/unbox axiom for Tclass._module.Even
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Even()) } 
  $IsBox(bx, Tclass._module.Even())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Even()));

// _module.Even: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.Even()) } 
  $Is(x#0, Tclass._module.Even()) <==> Mod(x#0, LitInt(2)) == LitInt(0));

// _module.Even: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.Even(), $h) } 
  $IsAlloc(x#0, Tclass._module.Even(), $h));

procedure CheckWellformed$$_module.Odd(x#0: int);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Odd(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type Odd
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(49,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assert LitInt(2) != 0;
        assume Mod(x#0, LitInt(2)) == LitInt(1);
    }
    else
    {
        assume true;
        assert LitInt(Mod(17, LitInt(2))) == LitInt(1);
    }
}



function Tclass._module.Odd() : Ty;

const unique Tagclass._module.Odd: TyTag;

// Tclass._module.Odd Tag
axiom Tag(Tclass._module.Odd()) == Tagclass._module.Odd
   && TagFamily(Tclass._module.Odd()) == tytagFamily$Odd;

// Box/unbox axiom for Tclass._module.Odd
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Odd()) } 
  $IsBox(bx, Tclass._module.Odd())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.Odd()));

// _module.Odd: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.Odd()) } 
  $Is(x#0, Tclass._module.Odd()) <==> Mod(x#0, LitInt(2)) == LitInt(1));

// _module.Odd: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.Odd(), $h) } 
  $IsAlloc(x#0, Tclass._module.Odd(), $h));

procedure CheckWellformed$$_module.GW(x#0: int);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.GW(x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for subset type GW
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(50,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assert LitInt(2) != 0;
        assume Mod(x#0, LitInt(2)) == LitInt(1);
    }
    else
    {
        assume true;
        assert LitInt(Mod(17, LitInt(2))) == LitInt(1);
    }
}



function Tclass._module.GW() : Ty;

const unique Tagclass._module.GW: TyTag;

// Tclass._module.GW Tag
axiom Tag(Tclass._module.GW()) == Tagclass._module.GW
   && TagFamily(Tclass._module.GW()) == tytagFamily$GW;

// Box/unbox axiom for Tclass._module.GW
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.GW()) } 
  $IsBox(bx, Tclass._module.GW())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass._module.GW()));

// _module.GW: subset type $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass._module.GW()) } 
  $Is(x#0, Tclass._module.GW()) <==> Mod(x#0, LitInt(2)) == LitInt(1));

// _module.GW: subset type $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass._module.GW(), $h) } 
  $IsAlloc(x#0, Tclass._module.GW(), $h));

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

// function declaration for _module._default.Yes
function _module.__default.Yes(six#0: int) : bool;

function _module.__default.Yes#canCall(six#0: int) : bool;

// consequence axiom for _module.__default.Yes
axiom 20 <= $FunctionContextHeight
   ==> (forall six#0: int :: 
    { _module.__default.Yes(six#0) } 
    _module.__default.Yes#canCall(six#0)
         || (20 != $FunctionContextHeight && LitInt(6) <= six#0)
       ==> true);

function _module.__default.Yes#requires(int) : bool;

// #requires axiom for _module.__default.Yes
axiom (forall six#0: int :: 
  { _module.__default.Yes#requires(six#0) } 
  LitInt(6) <= six#0 ==> _module.__default.Yes#requires(six#0) == true);

// definition axiom for _module.__default.Yes (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall six#0: int :: 
    { _module.__default.Yes(six#0) } 
    _module.__default.Yes#canCall(six#0)
         || (20 != $FunctionContextHeight && LitInt(6) <= six#0)
       ==> _module.__default.Yes(six#0) == (LitInt(4) <= six#0));

// definition axiom for _module.__default.Yes for all literals (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall six#0: int :: 
    {:weight 3} { _module.__default.Yes(LitInt(six#0)) } 
    _module.__default.Yes#canCall(LitInt(six#0))
         || (20 != $FunctionContextHeight && LitInt(6) <= six#0)
       ==> _module.__default.Yes(LitInt(six#0)) == (LitInt(4) <= LitInt(six#0)));

procedure CheckWellformed$$_module.__default.Yes(six#0: int where LitInt(6) <= six#0);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.Length
function _module.__default.Length(_module._default.Length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType) : int;

function _module.__default.Length#canCall(_module._default.Length$_T0: Ty, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.Length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.Length(_module._default.Length$_T0, $LS($ly), xs#0) } 
  _module.__default.Length(_module._default.Length$_T0, $LS($ly), xs#0)
     == _module.__default.Length(_module._default.Length$_T0, $ly, xs#0));

// fuel synonym axiom
axiom (forall _module._default.Length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.Length(_module._default.Length$_T0, AsFuelBottom($ly), xs#0) } 
  _module.__default.Length(_module._default.Length$_T0, $ly, xs#0)
     == _module.__default.Length(_module._default.Length$_T0, $LZ, xs#0));

// consequence axiom for _module.__default.Length
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.Length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.Length(_module._default.Length$_T0, $ly, xs#0) } 
    _module.__default.Length#canCall(_module._default.Length$_T0, xs#0)
         || (11 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.Length$_T0)))
       ==> LitInt(0) <= _module.__default.Length(_module._default.Length$_T0, $ly, xs#0));

function _module.__default.Length#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.Length
axiom (forall _module._default.Length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.Length#requires(_module._default.Length$_T0, $ly, xs#0) } 
  $Is(xs#0, Tclass._module.List(_module._default.Length$_T0))
     ==> _module.__default.Length#requires(_module._default.Length$_T0, $ly, xs#0)
       == true);

// definition axiom for _module.__default.Length (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.Length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.Length(_module._default.Length$_T0, $LS($ly), xs#0) } 
    _module.__default.Length#canCall(_module._default.Length$_T0, xs#0)
         || (11 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.Length$_T0)))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var tail#1 := _module.List._h1(xs#0); 
            _module.__default.Length#canCall(_module._default.Length$_T0, tail#1)))
         && _module.__default.Length(_module._default.Length$_T0, $LS($ly), xs#0)
           == (if _module.List.Nil_q(xs#0)
             then 0
             else (var tail#0 := _module.List._h1(xs#0); 
              _module.__default.Length(_module._default.Length$_T0, $ly, tail#0) + 1)));

// definition axiom for _module.__default.Length for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.Length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.Length(_module._default.Length$_T0, $LS($ly), Lit(xs#0)) } 
    _module.__default.Length#canCall(_module._default.Length$_T0, Lit(xs#0))
         || (11 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.Length$_T0)))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var tail#3 := Lit(_module.List._h1(Lit(xs#0))); 
            _module.__default.Length#canCall(_module._default.Length$_T0, tail#3)))
         && _module.__default.Length(_module._default.Length$_T0, $LS($ly), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then 0
             else (var tail#2 := Lit(_module.List._h1(Lit(xs#0))); 
              LitInt(_module.__default.Length(_module._default.Length$_T0, $LS($ly), tail#2) + 1))));

procedure CheckWellformed$$_module.__default.Length(_module._default.Length$_T0: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.Length$_T0)));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Length(_module._default.Length$_T0: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Length
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(29,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0)
           <= _module.__default.Length(_module._default.Length$_T0, $LS($LZ), xs#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assert $Is(LitInt(0), Tclass._System.nat());
            assume _module.__default.Length(_module._default.Length$_T0, $LS($LZ), xs#0)
               == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Length(_module._default.Length$_T0, $LS($LZ), xs#0), 
              Tclass._System.nat());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.Length$_T0);
            assume $Is(_mcc#1#0, Tclass._module.List(_module._default.Length$_T0));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.List(_module._default.Length$_T0));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List(_module._default.Length$_T0));
            assume tail#Z#0 == let#0#0#0;
            ##xs#0 := tail#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(_module._default.Length$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##xs#0) < DtRank(xs#0);
            assume _module.__default.Length#canCall(_module._default.Length$_T0, tail#Z#0);
            assert $Is(_module.__default.Length(_module._default.Length$_T0, $LS($LZ), tail#Z#0) + 1, 
              Tclass._System.nat());
            assume _module.__default.Length(_module._default.Length$_T0, $LS($LZ), xs#0)
               == _module.__default.Length(_module._default.Length$_T0, $LS($LZ), tail#Z#0) + 1;
            assume _module.__default.Length#canCall(_module._default.Length$_T0, tail#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Length(_module._default.Length$_T0, $LS($LZ), xs#0), 
              Tclass._System.nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.DefiniteAssignmentViolation()
   returns (e#0: DatatypeType
       where $Is(e#0, Tclass._module.Yt(Tclass._module.Even()))
         && $IsAlloc(e#0, Tclass._module.Yt(Tclass._module.Even()), $Heap), 
    o#0: DatatypeType
       where $Is(o#0, Tclass._module.Yt(Tclass._module.Odd()))
         && $IsAlloc(o#0, Tclass._module.Yt(Tclass._module.Odd()), $Heap), 
    g#0: DatatypeType
       where $Is(g#0, Tclass._module.Yt(Tclass._module.GW()))
         && $IsAlloc(g#0, Tclass._module.Yt(Tclass._module.GW()), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.DefiniteAssignmentViolation()
   returns (e#0: DatatypeType
       where $Is(e#0, Tclass._module.Yt(Tclass._module.Even()))
         && $IsAlloc(e#0, Tclass._module.Yt(Tclass._module.Even()), $Heap), 
    o#0: DatatypeType
       where $Is(o#0, Tclass._module.Yt(Tclass._module.Odd()))
         && $IsAlloc(o#0, Tclass._module.Yt(Tclass._module.Odd()), $Heap), 
    g#0: DatatypeType
       where $Is(g#0, Tclass._module.Yt(Tclass._module.GW()))
         && $IsAlloc(g#0, Tclass._module.Yt(Tclass._module.GW()), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.DefiniteAssignmentViolation()
   returns (e#0: DatatypeType
       where $Is(e#0, Tclass._module.Yt(Tclass._module.Even()))
         && $IsAlloc(e#0, Tclass._module.Yt(Tclass._module.Even()), $Heap), 
    o#0: DatatypeType
       where $Is(o#0, Tclass._module.Yt(Tclass._module.Odd()))
         && $IsAlloc(o#0, Tclass._module.Yt(Tclass._module.Odd()), $Heap), 
    defass#g#0: bool, 
    g#0: DatatypeType
       where defass#g#0
         ==> $Is(g#0, Tclass._module.Yt(Tclass._module.GW()))
           && $IsAlloc(g#0, Tclass._module.Yt(Tclass._module.GW()), $Heap), 
    $_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.DefiniteAssignmentViolation()
   returns (e#0: DatatypeType, 
    o#0: DatatypeType, 
    defass#g#0: bool, 
    g#0: DatatypeType, 
    $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: DefiniteAssignmentViolation, Impl$$_module.__default.DefiniteAssignmentViolation
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(52,0): initial state"} true;
    $_reverifyPost := false;
    assert defass#g#0;
}



procedure CheckWellformed$$_module.__default.ArrayElementInitViolation()
   returns (e#0: ref
       where $Is(e#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Even())))
         && $IsAlloc(e#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Even())), $Heap), 
    o#0: ref
       where $Is(o#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Odd())))
         && $IsAlloc(o#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Odd())), $Heap), 
    g#0: ref
       where $Is(g#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.GW())))
         && $IsAlloc(g#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.GW())), $Heap));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ArrayElementInitViolation()
   returns (e#0: ref
       where $Is(e#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Even())))
         && $IsAlloc(e#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Even())), $Heap), 
    o#0: ref
       where $Is(o#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Odd())))
         && $IsAlloc(o#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Odd())), $Heap), 
    g#0: ref
       where $Is(g#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.GW())))
         && $IsAlloc(g#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.GW())), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.ArrayElementInitViolation()
   returns (e#0: ref
       where $Is(e#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Even())))
         && $IsAlloc(e#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Even())), $Heap), 
    o#0: ref
       where $Is(o#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Odd())))
         && $IsAlloc(o#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.Odd())), $Heap), 
    g#0: ref
       where $Is(g#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.GW())))
         && $IsAlloc(g#0, Tclass._System.array(Tclass._module.Yt(Tclass._module.GW())), $Heap), 
    $_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.ArrayElementInitViolation() returns (e#0: ref, o#0: ref, g#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;

    // AddMethodImpl: ArrayElementInitViolation, Impl$$_module.__default.ArrayElementInitViolation
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(55,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(56,5)
    assume true;
    assert 0 <= LitInt(20);
    havoc $nw;
    assume $nw != null
       && dtype($nw) == Tclass._System.array?(Tclass._module.Yt(Tclass._module.Even()));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(20);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    e#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(56,23)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(57,5)
    assume true;
    assert 0 <= LitInt(20);
    havoc $nw;
    assume $nw != null
       && dtype($nw) == Tclass._System.array?(Tclass._module.Yt(Tclass._module.Odd()));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(20);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    o#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(57,22)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(58,5)
    assume true;
    assert 0 <= LitInt(20);
    assert 0 == LitInt(20);
    havoc $nw;
    assume $nw != null
       && dtype($nw) == Tclass._System.array?(Tclass._module.Yt(Tclass._module.GW()));
    assume !read($Heap, $nw, alloc);
    assume _System.array.Length($nw) == LitInt(20);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    g#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/NonZeroInitialization.dfy(58,21)"} true;
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

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$MyInt_Bad: TyTagFamily;

const unique tytagFamily$MyInt: TyTagFamily;

const unique tytagFamily$MyNewInt: TyTagFamily;

const unique tytagFamily$Six: TyTagFamily;

const unique tytagFamily$SixAgain: TyTagFamily;

const unique tytagFamily$SixAgainW: TyTagFamily;

const unique tytagFamily$Impossible: TyTagFamily;

const unique tytagFamily$NewSix: TyTagFamily;

const unique tytagFamily$NewSixAgain: TyTagFamily;

const unique tytagFamily$NewSixAgainW: TyTagFamily;

const unique tytagFamily$NewSixAgainY: TyTagFamily;

const unique tytagFamily$NewImpossible: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$ListTwo: TyTagFamily;

const unique tytagFamily$TwoAgain: TyTagFamily;

const unique tytagFamily$TwoAgainW: TyTagFamily;

const unique tytagFamily$TwoImpossible: TyTagFamily;

const unique tytagFamily$ListFour: TyTagFamily;

const unique tytagFamily$ListFour': TyTagFamily;

const unique tytagFamily$Yt: TyTagFamily;

const unique tytagFamily$Even: TyTagFamily;

const unique tytagFamily$Odd: TyTagFamily;

const unique tytagFamily$GW: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
