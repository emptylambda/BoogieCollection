// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy -print:./RollYourOwnArrowType.bpl

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

procedure CheckWellformed$$_module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A: Ty, 
    _module.NoWitness_EffectlessArrow$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B)));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A: Ty, 
    _module.NoWitness_EffectlessArrow$B: Ty, 
    f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Box;
  var ##x0#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type NoWitness_EffectlessArrow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(6,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        havoc a#0;
        assume $IsBox(a#0, _module.NoWitness_EffectlessArrow$A);
        ##x0#0 := a#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#0, _module.NoWitness_EffectlessArrow$A, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module.NoWitness_EffectlessArrow$A, 
                _module.NoWitness_EffectlessArrow$B, 
                $Heap, 
                f#0, 
                ##x0#0)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Reads1#canCall(_module.NoWitness_EffectlessArrow$A, 
          _module.NoWitness_EffectlessArrow$B, 
          $Heap, 
          f#0, 
          a#0);
        assume Set#Equal(Reads1(_module.NoWitness_EffectlessArrow$A, 
            _module.NoWitness_EffectlessArrow$B, 
            $Heap, 
            f#0, 
            a#0), 
          Set#Empty(): Set Box);
        assume (forall a#1: Box :: 
          $IsBox(a#1, _module.NoWitness_EffectlessArrow$A)
             ==> Set#Equal(Reads1(_module.NoWitness_EffectlessArrow$A, 
                _module.NoWitness_EffectlessArrow$B, 
                $Heap, 
                f#0, 
                a#1), 
              Set#Empty(): Set Box));
        assert b$reqreads#0;
    }
    else
    {
        assert false;
    }
}



function Tclass._module.NoWitness__EffectlessArrow(Ty, Ty) : Ty;

const unique Tagclass._module.NoWitness__EffectlessArrow: TyTag;

// Tclass._module.NoWitness__EffectlessArrow Tag
axiom (forall _module.NoWitness_EffectlessArrow$A: Ty, _module.NoWitness_EffectlessArrow$B: Ty :: 
  { Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B) } 
  Tag(Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B))
       == Tagclass._module.NoWitness__EffectlessArrow
     && TagFamily(Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B))
       == tytagFamily$NoWitness_EffectlessArrow);

// Tclass._module.NoWitness__EffectlessArrow injectivity 0
axiom (forall _module.NoWitness_EffectlessArrow$A: Ty, _module.NoWitness_EffectlessArrow$B: Ty :: 
  { Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B) } 
  Tclass._module.NoWitness__EffectlessArrow_0(Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B))
     == _module.NoWitness_EffectlessArrow$A);

function Tclass._module.NoWitness__EffectlessArrow_0(Ty) : Ty;

// Tclass._module.NoWitness__EffectlessArrow injectivity 1
axiom (forall _module.NoWitness_EffectlessArrow$A: Ty, _module.NoWitness_EffectlessArrow$B: Ty :: 
  { Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B) } 
  Tclass._module.NoWitness__EffectlessArrow_1(Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B))
     == _module.NoWitness_EffectlessArrow$B);

function Tclass._module.NoWitness__EffectlessArrow_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.NoWitness__EffectlessArrow
axiom (forall _module.NoWitness_EffectlessArrow$A: Ty, 
    _module.NoWitness_EffectlessArrow$B: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B)) } 
  $IsBox(bx, 
      Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B)));

// _module.NoWitness_EffectlessArrow: subset type $Is
axiom (forall _module.NoWitness_EffectlessArrow$A: Ty, 
    _module.NoWitness_EffectlessArrow$B: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B)) } 
  $Is(f#0, 
      Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B))
     <==> $Is(f#0, 
        Tclass._System.___hFunc1(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B))
       && (forall a#1: Box :: 
        $IsBox(a#1, _module.NoWitness_EffectlessArrow$A)
           ==> Set#Equal(Reads1(_module.NoWitness_EffectlessArrow$A, 
              _module.NoWitness_EffectlessArrow$B, 
              $OneHeap, 
              f#0, 
              a#1), 
            Set#Empty(): Set Box)));

// _module.NoWitness_EffectlessArrow: subset type $IsAlloc
axiom (forall _module.NoWitness_EffectlessArrow$A: Ty, 
    _module.NoWitness_EffectlessArrow$B: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._module.NoWitness__EffectlessArrow(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hFunc1(_module.NoWitness_EffectlessArrow$A, _module.NoWitness_EffectlessArrow$B), 
      $h));

procedure CheckWellformed$$_module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A: Ty, 
    _module.NonGhost_EffectlessArrow$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B)));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



function _module.__default.EffectlessArrowWitness#Handle(Ty, Ty) : HandleType;

axiom (forall _module._default.EffectlessArrowWitness$A: Ty, 
    _module._default.EffectlessArrowWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Apply1(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $heap, 
      _module.__default.EffectlessArrowWitness#Handle(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B), 
      $fh$0x#0) } 
  Apply1(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $heap, 
      _module.__default.EffectlessArrowWitness#Handle(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B), 
      $fh$0x#0)
     == _module.__default.EffectlessArrowWitness(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $fh$0x#0));

axiom (forall _module._default.EffectlessArrowWitness$A: Ty, 
    _module._default.EffectlessArrowWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Requires1(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $heap, 
      _module.__default.EffectlessArrowWitness#Handle(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B), 
      $fh$0x#0) } 
  Requires1(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $heap, 
      _module.__default.EffectlessArrowWitness#Handle(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B), 
      $fh$0x#0)
     == _module.__default.EffectlessArrowWitness#requires(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $fh$0x#0));

axiom (forall $bx: Box, 
    _module._default.EffectlessArrowWitness$A: Ty, 
    _module._default.EffectlessArrowWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Reads1(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $heap, 
      _module.__default.EffectlessArrowWitness#Handle(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B), 
      $fh$0x#0)[$bx] } 
  Reads1(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $heap, 
      _module.__default.EffectlessArrowWitness#Handle(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B), 
      $fh$0x#0)[$bx]
     == false);

axiom (forall _module._default.EffectlessArrowWitness$A: Ty, 
    _module._default.EffectlessArrowWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { _module.__default.EffectlessArrowWitness(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $fh$0x#0), $IsGoodHeap($heap) } 
  _module.__default.EffectlessArrowWitness(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $fh$0x#0)
     == Apply1(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      $heap, 
      _module.__default.EffectlessArrowWitness#Handle(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B), 
      $fh$0x#0));

implementation CheckWellformed$$_module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A: Ty, 
    _module.NonGhost_EffectlessArrow$B: Ty, 
    f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Box;
  var ##x0#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type NonGhost_EffectlessArrow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(9,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        havoc a#0;
        assume $IsBox(a#0, _module.NonGhost_EffectlessArrow$A);
        ##x0#0 := a#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#0, _module.NonGhost_EffectlessArrow$A, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module.NonGhost_EffectlessArrow$A, 
                _module.NonGhost_EffectlessArrow$B, 
                $Heap, 
                f#0, 
                ##x0#0)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Reads1#canCall(_module.NonGhost_EffectlessArrow$A, 
          _module.NonGhost_EffectlessArrow$B, 
          $Heap, 
          f#0, 
          a#0);
        assume Set#Equal(Reads1(_module.NonGhost_EffectlessArrow$A, 
            _module.NonGhost_EffectlessArrow$B, 
            $Heap, 
            f#0, 
            a#0), 
          Set#Empty(): Set Box);
        assume (forall a#1: Box :: 
          $IsBox(a#1, _module.NonGhost_EffectlessArrow$A)
             ==> Set#Equal(Reads1(_module.NonGhost_EffectlessArrow$A, 
                _module.NonGhost_EffectlessArrow$B, 
                $Heap, 
                f#0, 
                a#1), 
              Set#Empty(): Set Box));
        assert b$reqreads#0;
    }
    else
    {
        assert 26 != $FunctionContextHeight;
        assume (forall a#2: Box :: 
          $IsBox(a#2, _module.NonGhost_EffectlessArrow$A)
             ==> Reads1#canCall(_module.NonGhost_EffectlessArrow$A, 
              _module.NonGhost_EffectlessArrow$B, 
              $Heap, 
              _module.__default.EffectlessArrowWitness#Handle(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B), 
              a#2));
        assert (forall a#2: Box :: 
          $IsBox(a#2, _module.NonGhost_EffectlessArrow$A)
             ==> Set#Equal(Reads1(_module.NonGhost_EffectlessArrow$A, 
                _module.NonGhost_EffectlessArrow$B, 
                $Heap, 
                _module.__default.EffectlessArrowWitness#Handle(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B), 
                a#2), 
              Set#Empty(): Set Box));
    }
}



function Tclass._module.NonGhost__EffectlessArrow(Ty, Ty) : Ty;

const unique Tagclass._module.NonGhost__EffectlessArrow: TyTag;

// Tclass._module.NonGhost__EffectlessArrow Tag
axiom (forall _module.NonGhost_EffectlessArrow$A: Ty, _module.NonGhost_EffectlessArrow$B: Ty :: 
  { Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B) } 
  Tag(Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B))
       == Tagclass._module.NonGhost__EffectlessArrow
     && TagFamily(Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B))
       == tytagFamily$NonGhost_EffectlessArrow);

// Tclass._module.NonGhost__EffectlessArrow injectivity 0
axiom (forall _module.NonGhost_EffectlessArrow$A: Ty, _module.NonGhost_EffectlessArrow$B: Ty :: 
  { Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B) } 
  Tclass._module.NonGhost__EffectlessArrow_0(Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B))
     == _module.NonGhost_EffectlessArrow$A);

function Tclass._module.NonGhost__EffectlessArrow_0(Ty) : Ty;

// Tclass._module.NonGhost__EffectlessArrow injectivity 1
axiom (forall _module.NonGhost_EffectlessArrow$A: Ty, _module.NonGhost_EffectlessArrow$B: Ty :: 
  { Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B) } 
  Tclass._module.NonGhost__EffectlessArrow_1(Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B))
     == _module.NonGhost_EffectlessArrow$B);

function Tclass._module.NonGhost__EffectlessArrow_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.NonGhost__EffectlessArrow
axiom (forall _module.NonGhost_EffectlessArrow$A: Ty, 
    _module.NonGhost_EffectlessArrow$B: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B)) } 
  $IsBox(bx, 
      Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B)));

// _module.NonGhost_EffectlessArrow: subset type $Is
axiom (forall _module.NonGhost_EffectlessArrow$A: Ty, 
    _module.NonGhost_EffectlessArrow$B: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B)) } 
  $Is(f#0, 
      Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B))
     <==> $Is(f#0, 
        Tclass._System.___hFunc1(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B))
       && (forall a#1: Box :: 
        $IsBox(a#1, _module.NonGhost_EffectlessArrow$A)
           ==> Set#Equal(Reads1(_module.NonGhost_EffectlessArrow$A, 
              _module.NonGhost_EffectlessArrow$B, 
              $OneHeap, 
              f#0, 
              a#1), 
            Set#Empty(): Set Box)));

// _module.NonGhost_EffectlessArrow: subset type $IsAlloc
axiom (forall _module.NonGhost_EffectlessArrow$A: Ty, 
    _module.NonGhost_EffectlessArrow$B: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._module.NonGhost__EffectlessArrow(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hFunc1(_module.NonGhost_EffectlessArrow$A, _module.NonGhost_EffectlessArrow$B), 
      $h));

procedure CheckWellformed$$_module.EffectlessArrow(_module.EffectlessArrow$A: Ty, 
    _module.EffectlessArrow$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module.EffectlessArrow$A, _module.EffectlessArrow$B)));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



function _module.__default.GhostEffectlessArrowWitness#Handle(Ty, Ty) : HandleType;

axiom (forall _module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Apply1(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $heap, 
      _module.__default.GhostEffectlessArrowWitness#Handle(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B), 
      $fh$0x#0) } 
  Apply1(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $heap, 
      _module.__default.GhostEffectlessArrowWitness#Handle(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B), 
      $fh$0x#0)
     == _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $fh$0x#0));

axiom (forall _module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Requires1(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $heap, 
      _module.__default.GhostEffectlessArrowWitness#Handle(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B), 
      $fh$0x#0) } 
  Requires1(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $heap, 
      _module.__default.GhostEffectlessArrowWitness#Handle(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B), 
      $fh$0x#0)
     == _module.__default.GhostEffectlessArrowWitness#requires(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $fh$0x#0));

axiom (forall $bx: Box, 
    _module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Reads1(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $heap, 
      _module.__default.GhostEffectlessArrowWitness#Handle(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B), 
      $fh$0x#0)[$bx] } 
  Reads1(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $heap, 
      _module.__default.GhostEffectlessArrowWitness#Handle(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B), 
      $fh$0x#0)[$bx]
     == false);

axiom (forall _module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $fh$0x#0), $IsGoodHeap($heap) } 
  _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $fh$0x#0)
     == Apply1(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      $heap, 
      _module.__default.GhostEffectlessArrowWitness#Handle(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B), 
      $fh$0x#0));

implementation CheckWellformed$$_module.EffectlessArrow(_module.EffectlessArrow$A: Ty, _module.EffectlessArrow$B: Ty, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Box;
  var ##x0#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type EffectlessArrow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(17,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        havoc a#0;
        assume $IsBox(a#0, _module.EffectlessArrow$A);
        ##x0#0 := a#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#0, _module.EffectlessArrow$A, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module.EffectlessArrow$A, _module.EffectlessArrow$B, $Heap, f#0, ##x0#0)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Reads1#canCall(_module.EffectlessArrow$A, _module.EffectlessArrow$B, $Heap, f#0, a#0);
        assume Set#Equal(Reads1(_module.EffectlessArrow$A, _module.EffectlessArrow$B, $Heap, f#0, a#0), 
          Set#Empty(): Set Box);
        assume (forall a#1: Box :: 
          $IsBox(a#1, _module.EffectlessArrow$A)
             ==> Set#Equal(Reads1(_module.EffectlessArrow$A, _module.EffectlessArrow$B, $Heap, f#0, a#1), 
              Set#Empty(): Set Box));
        assert b$reqreads#0;
    }
    else
    {
        assert 0 != $FunctionContextHeight;
        assume (forall a#2: Box :: 
          $IsBox(a#2, _module.EffectlessArrow$A)
             ==> Reads1#canCall(_module.EffectlessArrow$A, 
              _module.EffectlessArrow$B, 
              $Heap, 
              _module.__default.GhostEffectlessArrowWitness#Handle(_module.EffectlessArrow$A, _module.EffectlessArrow$B), 
              a#2));
        assert (forall a#2: Box :: 
          $IsBox(a#2, _module.EffectlessArrow$A)
             ==> Set#Equal(Reads1(_module.EffectlessArrow$A, 
                _module.EffectlessArrow$B, 
                $Heap, 
                _module.__default.GhostEffectlessArrowWitness#Handle(_module.EffectlessArrow$A, _module.EffectlessArrow$B), 
                a#2), 
              Set#Empty(): Set Box));
    }
}



function Tclass._module.EffectlessArrow(Ty, Ty) : Ty;

const unique Tagclass._module.EffectlessArrow: TyTag;

// Tclass._module.EffectlessArrow Tag
axiom (forall _module.EffectlessArrow$A: Ty, _module.EffectlessArrow$B: Ty :: 
  { Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B) } 
  Tag(Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B))
       == Tagclass._module.EffectlessArrow
     && TagFamily(Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B))
       == tytagFamily$EffectlessArrow);

// Tclass._module.EffectlessArrow injectivity 0
axiom (forall _module.EffectlessArrow$A: Ty, _module.EffectlessArrow$B: Ty :: 
  { Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B) } 
  Tclass._module.EffectlessArrow_0(Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B))
     == _module.EffectlessArrow$A);

function Tclass._module.EffectlessArrow_0(Ty) : Ty;

// Tclass._module.EffectlessArrow injectivity 1
axiom (forall _module.EffectlessArrow$A: Ty, _module.EffectlessArrow$B: Ty :: 
  { Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B) } 
  Tclass._module.EffectlessArrow_1(Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B))
     == _module.EffectlessArrow$B);

function Tclass._module.EffectlessArrow_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.EffectlessArrow
axiom (forall _module.EffectlessArrow$A: Ty, _module.EffectlessArrow$B: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B)) } 
  $IsBox(bx, 
      Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B)));

// _module.EffectlessArrow: subset type $Is
axiom (forall _module.EffectlessArrow$A: Ty, _module.EffectlessArrow$B: Ty, f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B)) } 
  $Is(f#0, 
      Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B))
     <==> $Is(f#0, 
        Tclass._System.___hFunc1(_module.EffectlessArrow$A, _module.EffectlessArrow$B))
       && (forall a#1: Box :: 
        $IsBox(a#1, _module.EffectlessArrow$A)
           ==> Set#Equal(Reads1(_module.EffectlessArrow$A, _module.EffectlessArrow$B, $OneHeap, f#0, a#1), 
            Set#Empty(): Set Box)));

// _module.EffectlessArrow: subset type $IsAlloc
axiom (forall _module.EffectlessArrow$A: Ty, 
    _module.EffectlessArrow$B: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._module.EffectlessArrow(_module.EffectlessArrow$A, _module.EffectlessArrow$B), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hFunc1(_module.EffectlessArrow$A, _module.EffectlessArrow$B), 
      $h));

procedure CheckWellformed$$_module.TotalArrow(_module.TotalArrow$A: Ty, 
    _module.TotalArrow$B: Ty, 
    f#0: HandleType
       where $Is(f#0, Tclass._module.EffectlessArrow(_module.TotalArrow$A, _module.TotalArrow$B)));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



function _module.__default.TotalWitness#Handle(Ty, Ty) : HandleType;

axiom (forall _module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Apply1(_module._default.TotalWitness$A, 
      _module._default.TotalWitness$B, 
      $heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitness$A, _module._default.TotalWitness$B), 
      $fh$0x#0) } 
  Apply1(_module._default.TotalWitness$A, 
      _module._default.TotalWitness$B, 
      $heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitness$A, _module._default.TotalWitness$B), 
      $fh$0x#0)
     == _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, $fh$0x#0));

axiom (forall _module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Requires1(_module._default.TotalWitness$A, 
      _module._default.TotalWitness$B, 
      $heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitness$A, _module._default.TotalWitness$B), 
      $fh$0x#0) } 
  Requires1(_module._default.TotalWitness$A, 
      _module._default.TotalWitness$B, 
      $heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitness$A, _module._default.TotalWitness$B), 
      $fh$0x#0)
     == _module.__default.TotalWitness#requires(_module._default.TotalWitness$A, _module._default.TotalWitness$B, $fh$0x#0));

axiom (forall $bx: Box, 
    _module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Reads1(_module._default.TotalWitness$A, 
      _module._default.TotalWitness$B, 
      $heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitness$A, _module._default.TotalWitness$B), 
      $fh$0x#0)[$bx] } 
  Reads1(_module._default.TotalWitness$A, 
      _module._default.TotalWitness$B, 
      $heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitness$A, _module._default.TotalWitness$B), 
      $fh$0x#0)[$bx]
     == false);

axiom (forall _module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, $fh$0x#0), $IsGoodHeap($heap) } 
  _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, $fh$0x#0)
     == Apply1(_module._default.TotalWitness$A, 
      _module._default.TotalWitness$B, 
      $heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitness$A, _module._default.TotalWitness$B), 
      $fh$0x#0));

implementation CheckWellformed$$_module.TotalArrow(_module.TotalArrow$A: Ty, _module.TotalArrow$B: Ty, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##f#0: HandleType;
  var b$reqreads#0: bool;
  var newtype$check#0: HandleType;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type TotalArrow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(77,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##f#0 := f#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#0, 
          Tclass._System.___hFunc1(_module.TotalArrow$A, _module.TotalArrow$B), 
          $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (exists _x0#0: Box, _o0#0: ref :: 
                $IsBox(_x0#0, _module.TotalArrow$A)
                   && $Is(_o0#0, Tclass._System.object?())
                   && Reads1(_module.TotalArrow$A, _module.TotalArrow$B, $Heap, ##f#0, _x0#0)[$Box(_o0#0)]
                   && $Box($o) == $Box(_o0#0))
             ==> $_Frame[$o, $f]);
        assume _module.__default.Total#canCall(_module.TotalArrow$A, _module.TotalArrow$B, $Heap, f#0);
        assume _module.__default.Total(_module.TotalArrow$A, _module.TotalArrow$B, $Heap, f#0);
        assert b$reqreads#0;
    }
    else
    {
        assert 3 != $FunctionContextHeight;
        newtype$check#0 := _module.__default.TotalWitness#Handle(_module.TotalArrow$A, _module.TotalArrow$B);
        assert (forall a#0: Box :: 
          $IsBox(a#0, _module.TotalArrow$A)
             ==> Set#Equal(Reads1(_module.TotalArrow$A, _module.TotalArrow$B, $Heap, newtype$check#0, a#0), 
              Set#Empty(): Set Box));
        assume _module.__default.Total#canCall(_module.TotalArrow$A, 
          _module.TotalArrow$B, 
          $Heap, 
          _module.__default.TotalWitness#Handle(_module.TotalArrow$A, _module.TotalArrow$B));
        assert {:subsumption 0} _module.__default.Total#canCall(_module.TotalArrow$A, 
            _module.TotalArrow$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module.TotalArrow$A, _module.TotalArrow$B))
           ==> _module.__default.Total(_module.TotalArrow$A, 
              _module.TotalArrow$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module.TotalArrow$A, _module.TotalArrow$B))
             || (forall a#1: Box :: 
              { Requires1(_module.TotalArrow$A, 
                  _module.TotalArrow$B, 
                  $Heap, 
                  _module.__default.TotalWitness#Handle(_module.TotalArrow$A, _module.TotalArrow$B), 
                  a#1) } 
                { Reads1(_module.TotalArrow$A, 
                  _module.TotalArrow$B, 
                  $Heap, 
                  _module.__default.TotalWitness#Handle(_module.TotalArrow$A, _module.TotalArrow$B), 
                  a#1) } 
              $IsBox(a#1, _module.TotalArrow$A)
                 ==> Set#Equal(Reads1(_module.TotalArrow$A, 
                      _module.TotalArrow$B, 
                      $Heap, 
                      _module.__default.TotalWitness#Handle(_module.TotalArrow$A, _module.TotalArrow$B), 
                      a#1), 
                    Set#Empty(): Set Box)
                   && Requires1(_module.TotalArrow$A, 
                    _module.TotalArrow$B, 
                    $Heap, 
                    _module.__default.TotalWitness#Handle(_module.TotalArrow$A, _module.TotalArrow$B), 
                    a#1));
    }
}



function Tclass._module.TotalArrow(Ty, Ty) : Ty;

const unique Tagclass._module.TotalArrow: TyTag;

// Tclass._module.TotalArrow Tag
axiom (forall _module.TotalArrow$A: Ty, _module.TotalArrow$B: Ty :: 
  { Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B) } 
  Tag(Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B))
       == Tagclass._module.TotalArrow
     && TagFamily(Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B))
       == tytagFamily$TotalArrow);

// Tclass._module.TotalArrow injectivity 0
axiom (forall _module.TotalArrow$A: Ty, _module.TotalArrow$B: Ty :: 
  { Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B) } 
  Tclass._module.TotalArrow_0(Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B))
     == _module.TotalArrow$A);

function Tclass._module.TotalArrow_0(Ty) : Ty;

// Tclass._module.TotalArrow injectivity 1
axiom (forall _module.TotalArrow$A: Ty, _module.TotalArrow$B: Ty :: 
  { Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B) } 
  Tclass._module.TotalArrow_1(Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B))
     == _module.TotalArrow$B);

function Tclass._module.TotalArrow_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.TotalArrow
axiom (forall _module.TotalArrow$A: Ty, _module.TotalArrow$B: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B)) } 
  $IsBox(bx, Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B)));

// _module.TotalArrow: subset type $Is
axiom (forall _module.TotalArrow$A: Ty, _module.TotalArrow$B: Ty, f#0: HandleType :: 
  { $Is(f#0, Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B)) } 
  $Is(f#0, Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B))
     <==> $Is(f#0, Tclass._module.EffectlessArrow(_module.TotalArrow$A, _module.TotalArrow$B))
       && _module.__default.Total(_module.TotalArrow$A, _module.TotalArrow$B, $OneHeap, f#0));

// _module.TotalArrow: subset type $IsAlloc
axiom (forall _module.TotalArrow$A: Ty, _module.TotalArrow$B: Ty, f#0: HandleType, $h: Heap :: 
  { $IsAlloc(f#0, Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B), $h) } 
  $IsAlloc(f#0, Tclass._module.TotalArrow(_module.TotalArrow$A, _module.TotalArrow$B), $h)
     <==> $IsAlloc(f#0, 
      Tclass._module.EffectlessArrow(_module.TotalArrow$A, _module.TotalArrow$B), 
      $h));

procedure CheckWellformed$$_module.DirectTotalArrow(_module.DirectTotalArrow$A: Ty, 
    _module.DirectTotalArrow$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._module.EffectlessArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B)));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.DirectTotalArrow(_module.DirectTotalArrow$A: Ty, _module.DirectTotalArrow$B: Ty, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var a#0: Box;
  var ##x0#0: Box;
  var b$reqreads#0: bool;
  var newtype$check#0: HandleType;

    b$reqreads#0 := true;

    // AddWellformednessCheck for subset type DirectTotalArrow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(98,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        havoc a#0;
        assume $IsBox(a#0, _module.DirectTotalArrow$A);
        ##x0#0 := a#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x0#0, _module.DirectTotalArrow$A, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B, $Heap, f#0, ##x0#0)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume Requires1#canCall(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B, $Heap, f#0, a#0);
        assume Requires1(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B, $Heap, f#0, a#0);
        assume (forall a#1: Box :: 
          $IsBox(a#1, _module.DirectTotalArrow$A)
             ==> Requires1(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B, $Heap, f#0, a#1));
        assert b$reqreads#0;
    }
    else
    {
        assert 3 != $FunctionContextHeight;
        newtype$check#0 := _module.__default.TotalWitness#Handle(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B);
        assert (forall a#2: Box :: 
          $IsBox(a#2, _module.DirectTotalArrow$A)
             ==> Set#Equal(Reads1(_module.DirectTotalArrow$A, 
                _module.DirectTotalArrow$B, 
                $Heap, 
                newtype$check#0, 
                a#2), 
              Set#Empty(): Set Box));
        assume (forall a#3: Box :: 
          $IsBox(a#3, _module.DirectTotalArrow$A)
             ==> Requires1#canCall(_module.DirectTotalArrow$A, 
              _module.DirectTotalArrow$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B), 
              a#3));
        assert (forall a#3: Box :: 
          $IsBox(a#3, _module.DirectTotalArrow$A)
             ==> Requires1(_module.DirectTotalArrow$A, 
              _module.DirectTotalArrow$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B), 
              a#3));
    }
}



function Tclass._module.DirectTotalArrow(Ty, Ty) : Ty;

const unique Tagclass._module.DirectTotalArrow: TyTag;

// Tclass._module.DirectTotalArrow Tag
axiom (forall _module.DirectTotalArrow$A: Ty, _module.DirectTotalArrow$B: Ty :: 
  { Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B) } 
  Tag(Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B))
       == Tagclass._module.DirectTotalArrow
     && TagFamily(Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B))
       == tytagFamily$DirectTotalArrow);

// Tclass._module.DirectTotalArrow injectivity 0
axiom (forall _module.DirectTotalArrow$A: Ty, _module.DirectTotalArrow$B: Ty :: 
  { Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B) } 
  Tclass._module.DirectTotalArrow_0(Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B))
     == _module.DirectTotalArrow$A);

function Tclass._module.DirectTotalArrow_0(Ty) : Ty;

// Tclass._module.DirectTotalArrow injectivity 1
axiom (forall _module.DirectTotalArrow$A: Ty, _module.DirectTotalArrow$B: Ty :: 
  { Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B) } 
  Tclass._module.DirectTotalArrow_1(Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B))
     == _module.DirectTotalArrow$B);

function Tclass._module.DirectTotalArrow_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.DirectTotalArrow
axiom (forall _module.DirectTotalArrow$A: Ty, _module.DirectTotalArrow$B: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B)) } 
  $IsBox(bx, 
      Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B)));

// _module.DirectTotalArrow: subset type $Is
axiom (forall _module.DirectTotalArrow$A: Ty, _module.DirectTotalArrow$B: Ty, f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B)) } 
  $Is(f#0, 
      Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B))
     <==> $Is(f#0, 
        Tclass._module.EffectlessArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B))
       && (forall a#1: Box :: 
        $IsBox(a#1, _module.DirectTotalArrow$A)
           ==> Requires1(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B, $OneHeap, f#0, a#1)));

// _module.DirectTotalArrow: subset type $IsAlloc
axiom (forall _module.DirectTotalArrow$A: Ty, 
    _module.DirectTotalArrow$B: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._module.DirectTotalArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._module.EffectlessArrow(_module.DirectTotalArrow$A, _module.DirectTotalArrow$B), 
      $h));

procedure CheckWellformed$$_module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A: Ty, 
    _module.TwoPred_TotalArrow$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B)));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A: Ty, 
    _module.TwoPred_TotalArrow$B: Ty, 
    f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##f#0: HandleType;
  var ##f#1: HandleType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for subset type TwoPred_TotalArrow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(126,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##f#0 := f#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#0, 
          Tclass._System.___hFunc1(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
          $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (exists _x0#0: Box, _o0#0: ref :: 
                $IsBox(_x0#0, _module.TwoPred_TotalArrow$A)
                   && $Is(_o0#0, Tclass._System.object?())
                   && Reads1(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B, $Heap, ##f#0, _x0#0)[$Box(_o0#0)]
                   && $Box($o) == $Box(_o0#0))
             ==> $_Frame[$o, $f]);
        assume _module.__default.EmptyReads#canCall(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B, $Heap, f#0);
        assume _module.__default.EmptyReads(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B, $Heap, f#0);
        ##f#1 := f#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#1, 
          Tclass._System.___hFunc1(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
          $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (exists _x1#0: Box, _o1#0: ref :: 
                $IsBox(_x1#0, _module.TwoPred_TotalArrow$A)
                   && $Is(_o1#0, Tclass._System.object?())
                   && Reads1(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B, $Heap, ##f#1, _x1#0)[$Box(_o1#0)]
                   && $Box($o) == $Box(_o1#0))
             ==> $_Frame[$o, $f]);
        assume _module.__default.TruePre#canCall(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B, $Heap, f#0);
        assume _module.__default.TruePre(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B, $Heap, f#0);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
    else
    {
        assert 3 != $FunctionContextHeight;
        assume _module.__default.EmptyReads#canCall(_module.TwoPred_TotalArrow$A, 
            _module.TwoPred_TotalArrow$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
           && (_module.__default.EmptyReads(_module.TwoPred_TotalArrow$A, 
              _module.TwoPred_TotalArrow$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
             ==> _module.__default.TruePre#canCall(_module.TwoPred_TotalArrow$A, 
              _module.TwoPred_TotalArrow$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B)));
        assert {:subsumption 0} _module.__default.EmptyReads#canCall(_module.TwoPred_TotalArrow$A, 
            _module.TwoPred_TotalArrow$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
           ==> _module.__default.EmptyReads(_module.TwoPred_TotalArrow$A, 
              _module.TwoPred_TotalArrow$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
             || (forall a#0: Box :: 
              { Reads1(_module.TwoPred_TotalArrow$A, 
                  _module.TwoPred_TotalArrow$B, 
                  $Heap, 
                  _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
                  a#0) } 
              $IsBox(a#0, _module.TwoPred_TotalArrow$A)
                 ==> Set#Equal(Reads1(_module.TwoPred_TotalArrow$A, 
                    _module.TwoPred_TotalArrow$B, 
                    $Heap, 
                    _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
                    a#0), 
                  Set#Empty(): Set Box));
        assert {:subsumption 0} _module.__default.TruePre#canCall(_module.TwoPred_TotalArrow$A, 
            _module.TwoPred_TotalArrow$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
           ==> _module.__default.TruePre(_module.TwoPred_TotalArrow$A, 
              _module.TwoPred_TotalArrow$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
             || (forall a#1: Box :: 
              { Requires1(_module.TwoPred_TotalArrow$A, 
                  _module.TwoPred_TotalArrow$B, 
                  $Heap, 
                  _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
                  a#1) } 
              $IsBox(a#1, _module.TwoPred_TotalArrow$A)
                 ==> Requires1(_module.TwoPred_TotalArrow$A, 
                  _module.TwoPred_TotalArrow$B, 
                  $Heap, 
                  _module.__default.TotalWitness#Handle(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
                  a#1));
    }
}



function Tclass._module.TwoPred__TotalArrow(Ty, Ty) : Ty;

const unique Tagclass._module.TwoPred__TotalArrow: TyTag;

// Tclass._module.TwoPred__TotalArrow Tag
axiom (forall _module.TwoPred_TotalArrow$A: Ty, _module.TwoPred_TotalArrow$B: Ty :: 
  { Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B) } 
  Tag(Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
       == Tagclass._module.TwoPred__TotalArrow
     && TagFamily(Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
       == tytagFamily$TwoPred_TotalArrow);

// Tclass._module.TwoPred__TotalArrow injectivity 0
axiom (forall _module.TwoPred_TotalArrow$A: Ty, _module.TwoPred_TotalArrow$B: Ty :: 
  { Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B) } 
  Tclass._module.TwoPred__TotalArrow_0(Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
     == _module.TwoPred_TotalArrow$A);

function Tclass._module.TwoPred__TotalArrow_0(Ty) : Ty;

// Tclass._module.TwoPred__TotalArrow injectivity 1
axiom (forall _module.TwoPred_TotalArrow$A: Ty, _module.TwoPred_TotalArrow$B: Ty :: 
  { Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B) } 
  Tclass._module.TwoPred__TotalArrow_1(Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
     == _module.TwoPred_TotalArrow$B);

function Tclass._module.TwoPred__TotalArrow_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.TwoPred__TotalArrow
axiom (forall _module.TwoPred_TotalArrow$A: Ty, _module.TwoPred_TotalArrow$B: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B)) } 
  $IsBox(bx, 
      Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B)));

// _module.TwoPred_TotalArrow: subset type $Is
axiom (forall _module.TwoPred_TotalArrow$A: Ty, 
    _module.TwoPred_TotalArrow$B: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B)) } 
  $Is(f#0, 
      Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
     <==> $Is(f#0, 
        Tclass._System.___hFunc1(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B))
       && 
      _module.__default.EmptyReads(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B, $OneHeap, f#0)
       && _module.__default.TruePre(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B, $OneHeap, f#0));

// _module.TwoPred_TotalArrow: subset type $IsAlloc
axiom (forall _module.TwoPred_TotalArrow$A: Ty, 
    _module.TwoPred_TotalArrow$B: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._module.TwoPred__TotalArrow(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hFunc1(_module.TwoPred_TotalArrow$A, _module.TwoPred_TotalArrow$B), 
      $h));

procedure CheckWellformed$$_module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A: Ty, 
    _module.Bad_TwoPred_TotalArrow$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B)));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



function _module.__default.PartialFunction#Handle(Ty, Ty) : HandleType;

axiom (forall _module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Apply1(_module._default.PartialFunction$A, 
      _module._default.PartialFunction$B, 
      $heap, 
      _module.__default.PartialFunction#Handle(_module._default.PartialFunction$A, _module._default.PartialFunction$B), 
      $fh$0x#0) } 
  Apply1(_module._default.PartialFunction$A, 
      _module._default.PartialFunction$B, 
      $heap, 
      _module.__default.PartialFunction#Handle(_module._default.PartialFunction$A, _module._default.PartialFunction$B), 
      $fh$0x#0)
     == _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, $fh$0x#0));

axiom (forall _module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Requires1(_module._default.PartialFunction$A, 
      _module._default.PartialFunction$B, 
      $heap, 
      _module.__default.PartialFunction#Handle(_module._default.PartialFunction$A, _module._default.PartialFunction$B), 
      $fh$0x#0) } 
  Requires1(_module._default.PartialFunction$A, 
      _module._default.PartialFunction$B, 
      $heap, 
      _module.__default.PartialFunction#Handle(_module._default.PartialFunction$A, _module._default.PartialFunction$B), 
      $fh$0x#0)
     == _module.__default.PartialFunction#requires(_module._default.PartialFunction$A, _module._default.PartialFunction$B, $fh$0x#0));

axiom (forall $bx: Box, 
    _module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { Reads1(_module._default.PartialFunction$A, 
      _module._default.PartialFunction$B, 
      $heap, 
      _module.__default.PartialFunction#Handle(_module._default.PartialFunction$A, _module._default.PartialFunction$B), 
      $fh$0x#0)[$bx] } 
  Reads1(_module._default.PartialFunction$A, 
      _module._default.PartialFunction$B, 
      $heap, 
      _module.__default.PartialFunction#Handle(_module._default.PartialFunction$A, _module._default.PartialFunction$B), 
      $fh$0x#0)[$bx]
     == false);

axiom (forall _module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    $heap: Heap, 
    $fh$0x#0: Box :: 
  { _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, $fh$0x#0), $IsGoodHeap($heap) } 
  _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, $fh$0x#0)
     == Apply1(_module._default.PartialFunction$A, 
      _module._default.PartialFunction$B, 
      $heap, 
      _module.__default.PartialFunction#Handle(_module._default.PartialFunction$A, _module._default.PartialFunction$B), 
      $fh$0x#0));

implementation CheckWellformed$$_module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A: Ty, 
    _module.Bad_TwoPred_TotalArrow$B: Ty, 
    f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##f#0: HandleType;
  var ##f#1: HandleType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for subset type Bad_TwoPred_TotalArrow
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(138,5): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        ##f#0 := f#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#0, 
          Tclass._System.___hFunc1(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
          $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (exists _x0#0: Box, _o0#0: ref :: 
                $IsBox(_x0#0, _module.Bad_TwoPred_TotalArrow$A)
                   && $Is(_o0#0, Tclass._System.object?())
                   && Reads1(_module.Bad_TwoPred_TotalArrow$A, 
                    _module.Bad_TwoPred_TotalArrow$B, 
                    $Heap, 
                    ##f#0, 
                    _x0#0)[$Box(_o0#0)]
                   && $Box($o) == $Box(_o0#0))
             ==> $_Frame[$o, $f]);
        assume _module.__default.EmptyReads#canCall(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B, $Heap, f#0);
        assume _module.__default.EmptyReads(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B, $Heap, f#0);
        ##f#1 := f#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#1, 
          Tclass._System.___hFunc1(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
          $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && (exists _x1#0: Box, _o1#0: ref :: 
                $IsBox(_x1#0, _module.Bad_TwoPred_TotalArrow$A)
                   && $Is(_o1#0, Tclass._System.object?())
                   && Reads1(_module.Bad_TwoPred_TotalArrow$A, 
                    _module.Bad_TwoPred_TotalArrow$B, 
                    $Heap, 
                    ##f#1, 
                    _x1#0)[$Box(_o1#0)]
                   && $Box($o) == $Box(_o1#0))
             ==> $_Frame[$o, $f]);
        assume _module.__default.TruePre#canCall(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B, $Heap, f#0);
        assume _module.__default.TruePre(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B, $Heap, f#0);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
    else
    {
        assert 24 != $FunctionContextHeight;
        assume _module.__default.EmptyReads#canCall(_module.Bad_TwoPred_TotalArrow$A, 
            _module.Bad_TwoPred_TotalArrow$B, 
            $Heap, 
            _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
           && (_module.__default.EmptyReads(_module.Bad_TwoPred_TotalArrow$A, 
              _module.Bad_TwoPred_TotalArrow$B, 
              $Heap, 
              _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
             ==> _module.__default.TruePre#canCall(_module.Bad_TwoPred_TotalArrow$A, 
              _module.Bad_TwoPred_TotalArrow$B, 
              $Heap, 
              _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B)));
        assert {:subsumption 0} _module.__default.EmptyReads#canCall(_module.Bad_TwoPred_TotalArrow$A, 
            _module.Bad_TwoPred_TotalArrow$B, 
            $Heap, 
            _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
           ==> _module.__default.EmptyReads(_module.Bad_TwoPred_TotalArrow$A, 
              _module.Bad_TwoPred_TotalArrow$B, 
              $Heap, 
              _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
             || (forall a#0: Box :: 
              { Reads1(_module.Bad_TwoPred_TotalArrow$A, 
                  _module.Bad_TwoPred_TotalArrow$B, 
                  $Heap, 
                  _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
                  a#0) } 
              $IsBox(a#0, _module.Bad_TwoPred_TotalArrow$A)
                 ==> Set#Equal(Reads1(_module.Bad_TwoPred_TotalArrow$A, 
                    _module.Bad_TwoPred_TotalArrow$B, 
                    $Heap, 
                    _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
                    a#0), 
                  Set#Empty(): Set Box));
        assert {:subsumption 0} _module.__default.TruePre#canCall(_module.Bad_TwoPred_TotalArrow$A, 
            _module.Bad_TwoPred_TotalArrow$B, 
            $Heap, 
            _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
           ==> _module.__default.TruePre(_module.Bad_TwoPred_TotalArrow$A, 
              _module.Bad_TwoPred_TotalArrow$B, 
              $Heap, 
              _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
             || (forall a#1: Box :: 
              { Requires1(_module.Bad_TwoPred_TotalArrow$A, 
                  _module.Bad_TwoPred_TotalArrow$B, 
                  $Heap, 
                  _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
                  a#1) } 
              $IsBox(a#1, _module.Bad_TwoPred_TotalArrow$A)
                 ==> Requires1(_module.Bad_TwoPred_TotalArrow$A, 
                  _module.Bad_TwoPred_TotalArrow$B, 
                  $Heap, 
                  _module.__default.PartialFunction#Handle(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
                  a#1));
    }
}



function Tclass._module.Bad__TwoPred__TotalArrow(Ty, Ty) : Ty;

const unique Tagclass._module.Bad__TwoPred__TotalArrow: TyTag;

// Tclass._module.Bad__TwoPred__TotalArrow Tag
axiom (forall _module.Bad_TwoPred_TotalArrow$A: Ty, _module.Bad_TwoPred_TotalArrow$B: Ty :: 
  { Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B) } 
  Tag(Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
       == Tagclass._module.Bad__TwoPred__TotalArrow
     && TagFamily(Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
       == tytagFamily$Bad_TwoPred_TotalArrow);

// Tclass._module.Bad__TwoPred__TotalArrow injectivity 0
axiom (forall _module.Bad_TwoPred_TotalArrow$A: Ty, _module.Bad_TwoPred_TotalArrow$B: Ty :: 
  { Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B) } 
  Tclass._module.Bad__TwoPred__TotalArrow_0(Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
     == _module.Bad_TwoPred_TotalArrow$A);

function Tclass._module.Bad__TwoPred__TotalArrow_0(Ty) : Ty;

// Tclass._module.Bad__TwoPred__TotalArrow injectivity 1
axiom (forall _module.Bad_TwoPred_TotalArrow$A: Ty, _module.Bad_TwoPred_TotalArrow$B: Ty :: 
  { Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B) } 
  Tclass._module.Bad__TwoPred__TotalArrow_1(Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
     == _module.Bad_TwoPred_TotalArrow$B);

function Tclass._module.Bad__TwoPred__TotalArrow_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Bad__TwoPred__TotalArrow
axiom (forall _module.Bad_TwoPred_TotalArrow$A: Ty, 
    _module.Bad_TwoPred_TotalArrow$B: Ty, 
    bx: Box :: 
  { $IsBox(bx, 
      Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B)) } 
  $IsBox(bx, 
      Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
     ==> $Box($Unbox(bx): HandleType) == bx
       && $Is($Unbox(bx): HandleType, 
        Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B)));

// _module.Bad_TwoPred_TotalArrow: subset type $Is
axiom (forall _module.Bad_TwoPred_TotalArrow$A: Ty, 
    _module.Bad_TwoPred_TotalArrow$B: Ty, 
    f#0: HandleType :: 
  { $Is(f#0, 
      Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B)) } 
  $Is(f#0, 
      Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
     <==> $Is(f#0, 
        Tclass._System.___hFunc1(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B))
       && 
      _module.__default.EmptyReads(_module.Bad_TwoPred_TotalArrow$A, 
        _module.Bad_TwoPred_TotalArrow$B, 
        $OneHeap, 
        f#0)
       && _module.__default.TruePre(_module.Bad_TwoPred_TotalArrow$A, 
        _module.Bad_TwoPred_TotalArrow$B, 
        $OneHeap, 
        f#0));

// _module.Bad_TwoPred_TotalArrow: subset type $IsAlloc
axiom (forall _module.Bad_TwoPred_TotalArrow$A: Ty, 
    _module.Bad_TwoPred_TotalArrow$B: Ty, 
    f#0: HandleType, 
    $h: Heap :: 
  { $IsAlloc(f#0, 
      Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
      $h) } 
  $IsAlloc(f#0, 
      Tclass._module.Bad__TwoPred__TotalArrow(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
      $h)
     <==> $IsAlloc(f#0, 
      Tclass._System.___hFunc1(_module.Bad_TwoPred_TotalArrow$A, _module.Bad_TwoPred_TotalArrow$B), 
      $h));

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

// function declaration for _module._default.EffectlessArrowWitness
function _module.__default.EffectlessArrowWitness(_module._default.EffectlessArrowWitness$A: Ty, 
    _module._default.EffectlessArrowWitness$B: Ty, 
    a#0: Box)
   : Box;

function _module.__default.EffectlessArrowWitness#canCall(_module._default.EffectlessArrowWitness$A: Ty, 
    _module._default.EffectlessArrowWitness$B: Ty, 
    a#0: Box)
   : bool;

// consequence axiom for _module.__default.EffectlessArrowWitness
axiom 26 <= $FunctionContextHeight
   ==> (forall _module._default.EffectlessArrowWitness$A: Ty, 
      _module._default.EffectlessArrowWitness$B: Ty, 
      a#0: Box :: 
    { _module.__default.EffectlessArrowWitness(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B, 
        a#0) } 
    _module.__default.EffectlessArrowWitness#canCall(_module._default.EffectlessArrowWitness$A, 
          _module._default.EffectlessArrowWitness$B, 
          a#0)
         || (26 != $FunctionContextHeight
           && $IsBox(a#0, _module._default.EffectlessArrowWitness$A))
       ==> $IsBox(_module.__default.EffectlessArrowWitness(_module._default.EffectlessArrowWitness$A, 
          _module._default.EffectlessArrowWitness$B, 
          a#0), 
        _module._default.EffectlessArrowWitness$B));

function _module.__default.EffectlessArrowWitness#requires(Ty, Ty, Box) : bool;

// #requires axiom for _module.__default.EffectlessArrowWitness
axiom (forall _module._default.EffectlessArrowWitness$A: Ty, 
    _module._default.EffectlessArrowWitness$B: Ty, 
    a#0: Box :: 
  { _module.__default.EffectlessArrowWitness#requires(_module._default.EffectlessArrowWitness$A, 
      _module._default.EffectlessArrowWitness$B, 
      a#0) } 
  $IsBox(a#0, _module._default.EffectlessArrowWitness$A)
     ==> _module.__default.EffectlessArrowWitness#requires(_module._default.EffectlessArrowWitness$A, 
        _module._default.EffectlessArrowWitness$B, 
        a#0)
       == true);

procedure CheckWellformed$$_module.__default.EffectlessArrowWitness(_module._default.EffectlessArrowWitness$A: Ty, 
    _module._default.EffectlessArrowWitness$B: Ty, 
    a#0: Box where $IsBox(a#0, _module._default.EffectlessArrowWitness$A));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.GhostEffectlessArrowWitness
function _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    a#0: Box)
   : Box;

function _module.__default.GhostEffectlessArrowWitness#canCall(_module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    a#0: Box)
   : bool;

// consequence axiom for _module.__default.GhostEffectlessArrowWitness
axiom 0 <= $FunctionContextHeight
   ==> (forall _module._default.GhostEffectlessArrowWitness$A: Ty, 
      _module._default.GhostEffectlessArrowWitness$B: Ty, 
      a#0: Box :: 
    { _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B, 
        a#0) } 
    _module.__default.GhostEffectlessArrowWitness#canCall(_module._default.GhostEffectlessArrowWitness$A, 
          _module._default.GhostEffectlessArrowWitness$B, 
          a#0)
         || (0 != $FunctionContextHeight
           && $IsBox(a#0, _module._default.GhostEffectlessArrowWitness$A))
       ==> $IsBox(_module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
          _module._default.GhostEffectlessArrowWitness$B, 
          a#0), 
        _module._default.GhostEffectlessArrowWitness$B));

function _module.__default.GhostEffectlessArrowWitness#requires(Ty, Ty, Box) : bool;

// #requires axiom for _module.__default.GhostEffectlessArrowWitness
axiom (forall _module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    $Heap: Heap, 
    a#0: Box :: 
  { _module.__default.GhostEffectlessArrowWitness#requires(_module._default.GhostEffectlessArrowWitness$A, 
      _module._default.GhostEffectlessArrowWitness$B, 
      a#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $IsBox(a#0, _module._default.GhostEffectlessArrowWitness$A)
     ==> _module.__default.GhostEffectlessArrowWitness#requires(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B, 
        a#0)
       == true);

function $let#0_b() : Box;

function $let#0$canCall() : bool;

axiom $let#0$canCall() ==> Lit(true);

// definition axiom for _module.__default.GhostEffectlessArrowWitness (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall _module._default.GhostEffectlessArrowWitness$A: Ty, 
      _module._default.GhostEffectlessArrowWitness$B: Ty, 
      $Heap: Heap, 
      a#0: Box :: 
    { _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B, 
        a#0), $IsGoodHeap($Heap) } 
    _module.__default.GhostEffectlessArrowWitness#canCall(_module._default.GhostEffectlessArrowWitness$A, 
          _module._default.GhostEffectlessArrowWitness$B, 
          a#0)
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $IsBox(a#0, _module._default.GhostEffectlessArrowWitness$A))
       ==> $let#0$canCall()
         && _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
            _module._default.GhostEffectlessArrowWitness$B, 
            a#0)
           == (var b#0 := $let#0_b(); b#0));

// definition axiom for _module.__default.GhostEffectlessArrowWitness for all literals (revealed)
axiom 0 <= $FunctionContextHeight
   ==> (forall _module._default.GhostEffectlessArrowWitness$A: Ty, 
      _module._default.GhostEffectlessArrowWitness$B: Ty, 
      $Heap: Heap, 
      a#0: Box :: 
    {:weight 3} { _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
        _module._default.GhostEffectlessArrowWitness$B, 
        Lit(a#0)), $IsGoodHeap($Heap) } 
    _module.__default.GhostEffectlessArrowWitness#canCall(_module._default.GhostEffectlessArrowWitness$A, 
          _module._default.GhostEffectlessArrowWitness$B, 
          Lit(a#0))
         || (0 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $IsBox(a#0, _module._default.GhostEffectlessArrowWitness$A))
       ==> $let#0$canCall()
         && _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
            _module._default.GhostEffectlessArrowWitness$B, 
            Lit(a#0))
           == (var b#1 := $let#0_b(); b#1));

procedure CheckWellformed$$_module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    a#0: Box where $IsBox(a#0, _module._default.GhostEffectlessArrowWitness$A));
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A: Ty, 
    _module._default.GhostEffectlessArrowWitness$B: Ty, 
    a#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#2: Box;


    // AddWellformednessCheck for function GhostEffectlessArrowWitness
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(21,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $IsBox(_module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
            _module._default.GhostEffectlessArrowWitness$B, 
            a#0), 
          _module._default.GhostEffectlessArrowWitness$B);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc b#2;
        if ($IsBox(b#2, _module._default.GhostEffectlessArrowWitness$B))
        {
        }

        assert true;
        assume $IsBox(b#2, _module._default.GhostEffectlessArrowWitness$B);
        assume true;
        assume $let#0$canCall();
        assume _module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
            _module._default.GhostEffectlessArrowWitness$B, 
            a#0)
           == b#2;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $IsBox(_module.__default.GhostEffectlessArrowWitness(_module._default.GhostEffectlessArrowWitness$A, 
            _module._default.GhostEffectlessArrowWitness$B, 
            a#0), 
          _module._default.GhostEffectlessArrowWitness$B);
    }
}



// function declaration for _module._default.Twice
function _module.__default.Twice(f#0: HandleType, x#0: int) : int;

function _module.__default.Twice#canCall(f#0: HandleType, x#0: int) : bool;

// consequence axiom for _module.__default.Twice
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.Twice(f#0, x#0), $IsGoodHeap($Heap) } 
    _module.__default.Twice#canCall(f#0, x#0)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
           && (forall x#1: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#1))))
       ==> true);

function _module.__default.Twice#requires(HandleType, int) : bool;

// #requires axiom for _module.__default.Twice
axiom (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
  { _module.__default.Twice#requires(f#0, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
     ==> _module.__default.Twice#requires(f#0, x#0)
       == (forall x#2: int :: 
        { Requires1(TInt, TInt, $Heap, f#0, $Box(x#2)) } 
        true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#2))));

// definition axiom for _module.__default.Twice (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.Twice(f#0, x#0), $IsGoodHeap($Heap) } 
    _module.__default.Twice#canCall(f#0, x#0)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
           && (forall x#2: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#2)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#2))))
       ==> _module.__default.Twice(f#0, x#0)
         == (var y#0 := $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int; 
          $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(y#0))): int));

// definition axiom for _module.__default.Twice for decreasing-related literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    {:weight 3} { _module.__default.Twice(f#0, LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.__default.Twice#canCall(f#0, LitInt(x#0))
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
           && (forall x#3: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#3)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#3))))
       ==> _module.__default.Twice(f#0, LitInt(x#0))
         == (var y#1 := $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(LitInt(x#0)))): int; 
          $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(y#1))): int));

// definition axiom for _module.__default.Twice for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    {:weight 3} { _module.__default.Twice(Lit(f#0), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.__default.Twice#canCall(Lit(f#0), LitInt(x#0))
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
           && (forall x#4: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#4)) } 
            true ==> Requires1(TInt, TInt, $Heap, Lit(f#0), $Box(x#4))))
       ==> _module.__default.Twice(Lit(f#0), LitInt(x#0))
         == (var y#2 := $Unbox(Apply1(TInt, TInt, $Heap, Lit(f#0), $Box(LitInt(x#0)))): int; 
          $Unbox(Apply1(TInt, TInt, $Heap, Lit(f#0), $Box(y#2))): int));

procedure CheckWellformed$$_module.__default.Twice(f#0: HandleType where $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt)), 
    x#0: int);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Twice(f#0: HandleType, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#5: int;
  var ##x0#0: int;
  var b$reqreads#0: bool;
  var y#Z#0: int;
  var let#0#0#0: int;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Twice
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(27,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    havoc x#5;
    assume true;
    ##x0#0 := x#5;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x0#0, TInt, $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#0, $Box(##x0#0))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume Requires1#canCall(TInt, TInt, $Heap, f#0, $Box(x#5));
    assume Requires1(TInt, TInt, $Heap, f#0, $Box(x#5));
    assume (forall x#6: int :: 
      { Requires1(TInt, TInt, $Heap, f#0, $Box(x#6)) } 
      true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#6)));
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc y#Z#0;
        assume true;
        assert Requires1(TInt, TInt, $Heap, f#0, $Box(x#0));
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, TInt, $Heap, f#0, $Box(x#0))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume let#0#0#0 == $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0#0#0, TInt);
        assume y#Z#0 == let#0#0#0;
        assert Requires1(TInt, TInt, $Heap, f#0, $Box(y#Z#0));
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, TInt, $Heap, f#0, $Box(y#Z#0))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume _module.__default.Twice(f#0, x#0)
           == $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(y#Z#0))): int;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Twice(f#0, x#0), TInt);
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.Twice'
function _module.__default.Twice_k($heap: Heap, f#0: HandleType, x#0: int) : int;

function _module.__default.Twice_k#canCall($heap: Heap, f#0: HandleType, x#0: int) : bool;

// frame axiom for _module.__default.Twice_k
axiom (forall $h0: Heap, $h1: Heap, f#0: HandleType, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.Twice_k($h1, f#0, x#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.Twice_k#canCall($h0, f#0, x#0)
         || $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (exists _x0#0: int, _o0#0: ref :: 
            $Is(_o0#0, Tclass._System.object?())
               && Reads1(TInt, TInt, $h0, f#0, $Box(_x0#0))[$Box(_o0#0)]
               && $Box($o) == $Box(_o0#0))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.Twice_k($h0, f#0, x#0)
       == _module.__default.Twice_k($h1, f#0, x#0));

// consequence axiom for _module.__default.Twice_k
axiom 7 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.Twice_k($Heap, f#0, x#0) } 
    _module.__default.Twice_k#canCall($Heap, f#0, x#0)
         || (7 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
           && (forall x#1: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#1))))
       ==> true);

function _module.__default.Twice_k#requires(Heap, HandleType, int) : bool;

// #requires axiom for _module.__default.Twice_k
axiom (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
  { _module.__default.Twice_k#requires($Heap, f#0, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
     ==> _module.__default.Twice_k#requires($Heap, f#0, x#0)
       == (forall x#2: int :: 
        { Requires1(TInt, TInt, $Heap, f#0, $Box(x#2)) } 
        true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#2))));

// definition axiom for _module.__default.Twice_k (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.Twice_k($Heap, f#0, x#0), $IsGoodHeap($Heap) } 
    _module.__default.Twice_k#canCall($Heap, f#0, x#0)
         || (7 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
           && (forall x#2: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#2)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#2))))
       ==> _module.__default.Twice_k($Heap, f#0, x#0)
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            f#0, 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int);

procedure CheckWellformed$$_module.__default.Twice_k(f#0: HandleType where $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt)), 
    x#0: int);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



function Reads1#Handle(Ty, Ty, HandleType) : HandleType;

axiom (forall #$T0: Ty, #$R: Ty, $self: HandleType, $heap: Heap, $fh$0x#0: Box :: 
  { Apply1(#$T0, 
      TSet(Tclass._System.object?()), 
      $heap, 
      Reads1#Handle(#$T0, #$R, $self), 
      $fh$0x#0) } 
  Apply1(#$T0, 
      TSet(Tclass._System.object?()), 
      $heap, 
      Reads1#Handle(#$T0, #$R, $self), 
      $fh$0x#0)
     == $Box(Reads1(#$T0, #$R, $heap, $self, $fh$0x#0)));

axiom (forall #$T0: Ty, #$R: Ty, $self: HandleType, $heap: Heap, $fh$0x#0: Box :: 
  { Requires1(#$T0, 
      TSet(Tclass._System.object?()), 
      $heap, 
      Reads1#Handle(#$T0, #$R, $self), 
      $fh$0x#0) } 
  Requires1(#$T0, 
      TSet(Tclass._System.object?()), 
      $heap, 
      Reads1#Handle(#$T0, #$R, $self), 
      $fh$0x#0)
     == true);

axiom (forall $bx: Box, #$T0: Ty, #$R: Ty, $self: HandleType, $heap: Heap, $fh$0x#0: Box :: 
  { Reads1(#$T0, 
      TSet(Tclass._System.object?()), 
      $heap, 
      Reads1#Handle(#$T0, #$R, $self), 
      $fh$0x#0)[$bx] } 
  Reads1(#$T0, 
      TSet(Tclass._System.object?()), 
      $heap, 
      Reads1#Handle(#$T0, #$R, $self), 
      $fh$0x#0)[$bx]
     == Reads1(#$T0, #$R, $heap, $self, $fh$0x#0)[$bx]);

axiom (forall #$T0: Ty, #$R: Ty, $self: HandleType, $heap: Heap, $fh$0x#0: Box :: 
  { Reads1(#$T0, #$R, $heap, $self, $fh$0x#0) } 
  Reads1(#$T0, #$R, $heap, $self, $fh$0x#0)
     == $Unbox(Apply1(#$T0, 
        TSet(Tclass._System.object?()), 
        $heap, 
        Reads1#Handle(#$T0, #$R, $self), 
        $fh$0x#0)): Set Box);

implementation CheckWellformed$$_module.__default.Twice_k(f#0: HandleType, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#3: int;
  var ##x0#0: int;
  var b$reqreads#0: bool;
  var _x0#1: int;
  var _o0#1: ref;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Twice'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(34,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (exists _x1#0: int, _o1#0: ref :: 
          $Is(_o1#0, Tclass._System.object?())
             && Reads1(TInt, TInt, $Heap, f#0, $Box(_x1#0))[$Box(_o1#0)]
             && $Box($o) == $Box(_o1#0)));
    havoc x#3;
    assume true;
    ##x0#0 := x#3;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x0#0, TInt, $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#0, $Box(##x0#0))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume Requires1#canCall(TInt, TInt, $Heap, f#0, $Box(x#3));
    assume Requires1(TInt, TInt, $Heap, f#0, $Box(x#3));
    assume (forall x#4: int :: 
      { Requires1(TInt, TInt, $Heap, f#0, $Box(x#4)) } 
      true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#4)));
    assert b$reqreads#0;
    assert true;
    // Begin Comprehension WF check
    havoc _x0#1;
    havoc _o0#1;
    if ($Is(_o0#1, Tclass._System.object?()))
    {
        assert true;
        assert Requires1(TInt, 
          TSet(Tclass._System.object?()), 
          $Heap, 
          Reads1#Handle(TInt, TInt, f#0), 
          $Box(_x0#1));
        if (Reads1(TInt, TInt, $Heap, f#0, $Box(_x0#1))[$Box(_o0#1)])
        {
        }
    }

    // End Comprehension WF check
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (exists _x2#0: int, _o2#0: ref :: 
              $Is(_o2#0, Tclass._System.object?())
                 && Reads1(TInt, TInt, $Heap, f#0, $Box(_x2#0))[$Box(_o2#0)]
                 && $Box($o) == $Box(_o2#0)));
        assert Requires1(TInt, TInt, $Heap, f#0, $Box(x#0));
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, TInt, $Heap, f#0, $Box(x#0))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert Requires1(TInt, 
          TInt, 
          $Heap, 
          f#0, 
          $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int));
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, 
                TInt, 
                $Heap, 
                f#0, 
                $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume _module.__default.Twice_k($Heap, f#0, x#0)
           == $Unbox(Apply1(TInt, 
              TInt, 
              $Heap, 
              f#0, 
              $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Twice_k($Heap, f#0, x#0), TInt);
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.Twice''
function _module.__default.Twice_k_k($heap: Heap, f#0: HandleType, x#0: int) : int;

function _module.__default.Twice_k_k#canCall($heap: Heap, f#0: HandleType, x#0: int) : bool;

// frame axiom for _module.__default.Twice_k_k
axiom (forall $h0: Heap, $h1: Heap, f#0: HandleType, x#0: int :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.Twice_k_k($h1, f#0, x#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.Twice_k_k#canCall($h0, f#0, x#0)
         || $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (exists _x0#0: int, _o0#0: ref :: 
            $Is(_o0#0, Tclass._System.object?())
               && Reads1(TInt, TInt, $h0, f#0, $Box(_x0#0))[$Box(_o0#0)]
               && $Box($o) == $Box(_o0#0))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.Twice_k_k($h0, f#0, x#0)
       == _module.__default.Twice_k_k($h1, f#0, x#0));

// consequence axiom for _module.__default.Twice_k_k
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.Twice_k_k($Heap, f#0, x#0) } 
    _module.__default.Twice_k_k#canCall($Heap, f#0, x#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
           && (forall x#1: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#1))))
       ==> true);

function _module.__default.Twice_k_k#requires(Heap, HandleType, int) : bool;

// #requires axiom for _module.__default.Twice_k_k
axiom (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
  { _module.__default.Twice_k_k#requires($Heap, f#0, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
     ==> _module.__default.Twice_k_k#requires($Heap, f#0, x#0)
       == (forall x#2: int :: 
        { Requires1(TInt, TInt, $Heap, f#0, $Box(x#2)) } 
        true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#2))));

// definition axiom for _module.__default.Twice_k_k (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.Twice_k_k($Heap, f#0, x#0), $IsGoodHeap($Heap) } 
    _module.__default.Twice_k_k#canCall($Heap, f#0, x#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt))
           && (forall x#2: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#2)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#2))))
       ==> _module.__default.Twice_k_k($Heap, f#0, x#0)
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            f#0, 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int);

procedure CheckWellformed$$_module.__default.Twice_k_k(f#0: HandleType where $Is(f#0, Tclass._module.EffectlessArrow(TInt, TInt)), 
    x#0: int);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Twice_k_k(f#0: HandleType, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#3: int;
  var ##x0#0: int;
  var b$reqreads#0: bool;
  var _x0#1: int;
  var _o0#1: ref;
  var ##x0#1: int;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Twice''
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(41,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (exists _x1#0: int, _o1#0: ref :: 
          $Is(_o1#0, Tclass._System.object?())
             && Reads1(TInt, TInt, $Heap, f#0, $Box(_x1#0))[$Box(_o1#0)]
             && $Box($o) == $Box(_o1#0)));
    havoc x#3;
    assume true;
    ##x0#0 := x#3;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x0#0, TInt, $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#0, $Box(##x0#0))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume Requires1#canCall(TInt, TInt, $Heap, f#0, $Box(x#3));
    assume Requires1(TInt, TInt, $Heap, f#0, $Box(x#3));
    assume (forall x#4: int :: 
      { Requires1(TInt, TInt, $Heap, f#0, $Box(x#4)) } 
      true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#4)));
    assert b$reqreads#0;
    assert true;
    // Begin Comprehension WF check
    havoc _x0#1;
    havoc _o0#1;
    if ($Is(_o0#1, Tclass._System.object?()))
    {
        assert true;
        assert Requires1(TInt, 
          TSet(Tclass._System.object?()), 
          $Heap, 
          Reads1#Handle(TInt, TInt, f#0), 
          $Box(_x0#1));
        if (Reads1(TInt, TInt, $Heap, f#0, $Box(_x0#1))[$Box(_o0#1)])
        {
        }
    }

    // End Comprehension WF check
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (exists _x2#0: int, _o2#0: ref :: 
              $Is(_o2#0, Tclass._System.object?())
                 && Reads1(TInt, TInt, $Heap, f#0, $Box(_x2#0))[$Box(_o2#0)]
                 && $Box($o) == $Box(_o2#0)));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(45,3)
        assert Requires1(TInt, TInt, $Heap, f#0, $Box(x#0));
        ##x0#1 := $Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x0#1, TInt, $Heap);
        assume Requires1#canCall(TInt, TInt, $Heap, f#0, Apply1(TInt, TInt, $Heap, f#0, $Box(x#0)));
        assume Requires1#canCall(TInt, TInt, $Heap, f#0, Apply1(TInt, TInt, $Heap, f#0, $Box(x#0)));
        assert Requires1(TInt, TInt, $Heap, f#0, Apply1(TInt, TInt, $Heap, f#0, $Box(x#0)));
        assert Requires1(TInt, TInt, $Heap, f#0, $Box(x#0));
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, TInt, $Heap, f#0, $Box(x#0))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert Requires1(TInt, 
          TInt, 
          $Heap, 
          f#0, 
          $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int));
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, 
                TInt, 
                $Heap, 
                f#0, 
                $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume _module.__default.Twice_k_k($Heap, f#0, x#0)
           == $Unbox(Apply1(TInt, 
              TInt, 
              $Heap, 
              f#0, 
              $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Twice_k_k($Heap, f#0, x#0), TInt);
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.TwoTimes
function _module.__default.TwoTimes(f#0: HandleType, x#0: int) : int;

function _module.__default.TwoTimes#canCall(f#0: HandleType, x#0: int) : bool;

// consequence axiom for _module.__default.TwoTimes
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.TwoTimes(f#0, x#0), $IsGoodHeap($Heap) } 
    _module.__default.TwoTimes#canCall(f#0, x#0)
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
           && 
          (forall x#1: int :: 
            { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
            true
               ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box))
           && (forall x#2: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#2)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#2))))
       ==> true);

function _module.__default.TwoTimes#requires(HandleType, int) : bool;

// #requires axiom for _module.__default.TwoTimes
axiom (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
  { _module.__default.TwoTimes#requires(f#0, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
     ==> _module.__default.TwoTimes#requires(f#0, x#0)
       == ((forall x#3: int :: 
          { Reads1(TInt, TInt, $Heap, f#0, $Box(x#3)) } 
          true
             ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#3)), Set#Empty(): Set Box))
         && (forall x#4: int :: 
          { Requires1(TInt, TInt, $Heap, f#0, $Box(x#4)) } 
          true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#4)))));

// definition axiom for _module.__default.TwoTimes (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.TwoTimes(f#0, x#0), $IsGoodHeap($Heap) } 
    _module.__default.TwoTimes#canCall(f#0, x#0)
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
           && 
          (forall x#3: int :: 
            { Reads1(TInt, TInt, $Heap, f#0, $Box(x#3)) } 
            true
               ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#3)), Set#Empty(): Set Box))
           && (forall x#4: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#4)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#4))))
       ==> _module.__default.TwoTimes(f#0, x#0)
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            f#0, 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int);

// definition axiom for _module.__default.TwoTimes for decreasing-related literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    {:weight 3} { _module.__default.TwoTimes(f#0, LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.__default.TwoTimes#canCall(f#0, LitInt(x#0))
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
           && 
          (forall x#5: int :: 
            { Reads1(TInt, TInt, $Heap, f#0, $Box(x#5)) } 
            true
               ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#5)), Set#Empty(): Set Box))
           && (forall x#6: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#6)) } 
            true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#6))))
       ==> _module.__default.TwoTimes(f#0, LitInt(x#0))
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            f#0, 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(LitInt(x#0)))): int))): int);

// definition axiom for _module.__default.TwoTimes for all literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    {:weight 3} { _module.__default.TwoTimes(Lit(f#0), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.__default.TwoTimes#canCall(Lit(f#0), LitInt(x#0))
         || (28 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
           && 
          (forall x#7: int :: 
            { Reads1(TInt, TInt, $Heap, f#0, $Box(x#7)) } 
            true
               ==> Set#Equal(Reads1(TInt, TInt, $Heap, Lit(f#0), $Box(x#7)), Set#Empty(): Set Box))
           && (forall x#8: int :: 
            { Requires1(TInt, TInt, $Heap, f#0, $Box(x#8)) } 
            true ==> Requires1(TInt, TInt, $Heap, Lit(f#0), $Box(x#8))))
       ==> _module.__default.TwoTimes(Lit(f#0), LitInt(x#0))
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            Lit(f#0), 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, Lit(f#0), $Box(LitInt(x#0)))): int))): int);

procedure CheckWellformed$$_module.__default.TwoTimes(f#0: HandleType where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt)), x#0: int);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TwoTimes(f#0: HandleType, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#9: int;
  var ##x0#0: int;
  var x#11: int;
  var ##x0#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function TwoTimes
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(49,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    havoc x#9;
    assume true;
    ##x0#0 := x#9;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x0#0, TInt, $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#0, $Box(##x0#0))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume Reads1#canCall(TInt, TInt, $Heap, f#0, $Box(x#9));
    assume Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#9)), Set#Empty(): Set Box);
    assume (forall x#10: int :: 
      { Reads1(TInt, TInt, $Heap, f#0, $Box(x#10)) } 
      true
         ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#10)), Set#Empty(): Set Box));
    havoc x#11;
    assume true;
    ##x0#1 := x#11;
    // assume allocatedness for argument to function
    assume $IsAlloc(##x0#1, TInt, $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && Reads1(TInt, TInt, $Heap, f#0, $Box(##x0#1))[$Box($o)]
         ==> $_Frame[$o, $f]);
    assume Requires1#canCall(TInt, TInt, $Heap, f#0, $Box(x#11));
    assume Requires1(TInt, TInt, $Heap, f#0, $Box(x#11));
    assume (forall x#12: int :: 
      { Requires1(TInt, TInt, $Heap, f#0, $Box(x#12)) } 
      true ==> Requires1(TInt, TInt, $Heap, f#0, $Box(x#12)));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert Requires1(TInt, TInt, $Heap, f#0, $Box(x#0));
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, TInt, $Heap, f#0, $Box(x#0))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert Requires1(TInt, 
          TInt, 
          $Heap, 
          f#0, 
          $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int));
        b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, 
                TInt, 
                $Heap, 
                f#0, 
                $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume _module.__default.TwoTimes(f#0, x#0)
           == $Unbox(Apply1(TInt, 
              TInt, 
              $Heap, 
              f#0, 
              $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.TwoTimes(f#0, x#0), TInt);
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module._default.Inc
function _module.__default.Inc(x#0: int) : int;

function _module.__default.Inc#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.Inc
axiom 29 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.Inc(x#0) } 
    _module.__default.Inc#canCall(x#0) || 29 != $FunctionContextHeight ==> true);

function _module.__default.Inc#requires(int) : bool;

// #requires axiom for _module.__default.Inc
axiom (forall x#0: int :: 
  { _module.__default.Inc#requires(x#0) } 
  _module.__default.Inc#requires(x#0) == true);

// definition axiom for _module.__default.Inc (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.Inc(x#0) } 
    _module.__default.Inc#canCall(x#0) || 29 != $FunctionContextHeight
       ==> _module.__default.Inc(x#0) == x#0 + 1);

// definition axiom for _module.__default.Inc for all literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.__default.Inc(LitInt(x#0)) } 
    _module.__default.Inc#canCall(LitInt(x#0)) || 29 != $FunctionContextHeight
       ==> _module.__default.Inc(LitInt(x#0)) == LitInt(x#0 + 1));

procedure CheckWellformed$$_module.__default.Inc(x#0: int);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default._default_Main();
  free requires 30 == $FunctionContextHeight;
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
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function _module.__default.Inc#Handle() : HandleType;

axiom (forall $heap: Heap, $fh$0x#0: Box :: 
  { Apply1(TInt, TInt, $heap, _module.__default.Inc#Handle(), $fh$0x#0) } 
  Apply1(TInt, TInt, $heap, _module.__default.Inc#Handle(), $fh$0x#0)
     == $Box(_module.__default.Inc($Unbox($fh$0x#0): int)));

axiom (forall $heap: Heap, $fh$0x#0: Box :: 
  { Requires1(TInt, TInt, $heap, _module.__default.Inc#Handle(), $fh$0x#0) } 
  Requires1(TInt, TInt, $heap, _module.__default.Inc#Handle(), $fh$0x#0)
     == _module.__default.Inc#requires($Unbox($fh$0x#0): int));

axiom (forall $bx: Box, $heap: Heap, $fh$0x#0: Box :: 
  { Reads1(TInt, TInt, $heap, _module.__default.Inc#Handle(), $fh$0x#0)[$bx] } 
  Reads1(TInt, TInt, $heap, _module.__default.Inc#Handle(), $fh$0x#0)[$bx]
     == false);

axiom (forall $heap: Heap, $fh$0x#0: int :: 
  { _module.__default.Inc($fh$0x#0), $IsGoodHeap($heap) } 
  _module.__default.Inc($fh$0x#0)
     == $Unbox(Apply1(TInt, TInt, $heap, _module.__default.Inc#Handle(), $Box($fh$0x#0))): int);

implementation Impl$$_module.__default._default_Main() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var y#0: int;
  var ##f#0: HandleType;
  var ##x#0: int;
  var z#0: int;
  var ##f#1: HandleType;
  var ##x#1: int;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(62,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(63,9)
    assume true;
    assert 29 != $FunctionContextHeight;
    ##f#0 := _module.__default.Inc#Handle();
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap);
    ##x#0 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, TInt, $Heap);
    assert {:subsumption 0} (forall x#0: int :: 
      { Reads1(TInt, TInt, $Heap, ##f#0, $Box(x#0)) } 
      true
         ==> Set#Equal(Reads1(TInt, TInt, $Heap, ##f#0, $Box(x#0)), Set#Empty(): Set Box));
    assume (forall x#0: int :: 
      { Reads1(TInt, TInt, $Heap, ##f#0, $Box(x#0)) } 
      true
         ==> Set#Equal(Reads1(TInt, TInt, $Heap, ##f#0, $Box(x#0)), Set#Empty(): Set Box));
    assert {:subsumption 0} (forall x#1: int :: 
      { Requires1(TInt, TInt, $Heap, ##f#0, $Box(x#1)) } 
      true ==> Requires1(TInt, TInt, $Heap, ##f#0, $Box(x#1)));
    assume (forall x#1: int :: 
      { Requires1(TInt, TInt, $Heap, ##f#0, $Box(x#1)) } 
      true ==> Requires1(TInt, TInt, $Heap, ##f#0, $Box(x#1)));
    assume _module.__default.TwoTimes#canCall(_module.__default.Inc#Handle(), LitInt(3));
    assume _module.__default.TwoTimes#canCall(_module.__default.Inc#Handle(), LitInt(3));
    y#0 := _module.__default.TwoTimes(_module.__default.Inc#Handle(), LitInt(3));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(63,27)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(64,3)
    assume true;
    assert y#0 == LitInt(5);
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(65,9)
    assume true;
    assert 29 != $FunctionContextHeight;
    assert $Is(_module.__default.Inc#Handle(), Tclass._module.EffectlessArrow(TInt, TInt));
    ##f#1 := _module.__default.Inc#Handle();
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#1, Tclass._module.EffectlessArrow(TInt, TInt), $Heap);
    ##x#1 := LitInt(12);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#1, TInt, $Heap);
    assert {:subsumption 0} (forall x#2: int :: 
      { Requires1(TInt, TInt, $Heap, ##f#1, $Box(x#2)) } 
      true ==> Requires1(TInt, TInt, $Heap, ##f#1, $Box(x#2)));
    assume (forall x#2: int :: 
      { Requires1(TInt, TInt, $Heap, ##f#1, $Box(x#2)) } 
      true ==> Requires1(TInt, TInt, $Heap, ##f#1, $Box(x#2)));
    assume _module.__default.Twice#canCall(_module.__default.Inc#Handle(), LitInt(12));
    assume _module.__default.Twice#canCall(_module.__default.Inc#Handle(), LitInt(12));
    z#0 := _module.__default.Twice(_module.__default.Inc#Handle(), LitInt(12));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(65,25)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(66,3)
    assume true;
    assert z#0 == LitInt(14);
}



// function declaration for _module._default.Total
function _module.__default.Total(_module._default.Total$A: Ty, 
    _module._default.Total$B: Ty, 
    $heap: Heap, 
    f#0: HandleType)
   : bool;

function _module.__default.Total#canCall(_module._default.Total$A: Ty, 
    _module._default.Total$B: Ty, 
    $heap: Heap, 
    f#0: HandleType)
   : bool;

// frame axiom for _module.__default.Total
axiom (forall _module._default.Total$A: Ty, 
    _module._default.Total$B: Ty, 
    $h0: Heap, 
    $h1: Heap, 
    f#0: HandleType :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.Total(_module._default.Total$A, _module._default.Total$B, $h1, f#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.Total#canCall(_module._default.Total$A, _module._default.Total$B, $h0, f#0)
         || $Is(f#0, 
          Tclass._System.___hFunc1(_module._default.Total$A, _module._default.Total$B)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (exists _x0#0: Box, _o0#0: ref :: 
            $IsBox(_x0#0, _module._default.Total$A)
               && $Is(_o0#0, Tclass._System.object?())
               && Reads1(_module._default.Total$A, _module._default.Total$B, $h0, f#0, _x0#0)[$Box(_o0#0)]
               && $Box($o) == $Box(_o0#0))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.Total(_module._default.Total$A, _module._default.Total$B, $h0, f#0)
       == _module.__default.Total(_module._default.Total$A, _module._default.Total$B, $h1, f#0));

// consequence axiom for _module.__default.Total
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.Total$A: Ty, 
      _module._default.Total$B: Ty, 
      $Heap: Heap, 
      f#0: HandleType :: 
    { _module.__default.Total(_module._default.Total$A, _module._default.Total$B, $Heap, f#0) } 
    _module.__default.Total#canCall(_module._default.Total$A, _module._default.Total$B, $Heap, f#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.Total$A, _module._default.Total$B)))
       ==> true);

function _module.__default.Total#requires(Ty, Ty, Heap, HandleType) : bool;

// #requires axiom for _module.__default.Total
axiom (forall _module._default.Total$A: Ty, 
    _module._default.Total$B: Ty, 
    $Heap: Heap, 
    f#0: HandleType :: 
  { _module.__default.Total#requires(_module._default.Total$A, _module._default.Total$B, $Heap, f#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.Total$A, _module._default.Total$B))
     ==> _module.__default.Total#requires(_module._default.Total$A, _module._default.Total$B, $Heap, f#0)
       == true);

// definition axiom for _module.__default.Total (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.Total$A: Ty, 
      _module._default.Total$B: Ty, 
      $Heap: Heap, 
      f#0: HandleType :: 
    { _module.__default.Total(_module._default.Total$A, _module._default.Total$B, $Heap, f#0), $IsGoodHeap($Heap) } 
    _module.__default.Total#canCall(_module._default.Total$A, _module._default.Total$B, $Heap, f#0)
         || (2 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.Total$A, _module._default.Total$B)))
       ==> (forall a#0: Box :: 
          { Requires1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0) } 
            { Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0) } 
          $IsBox(a#0, _module._default.Total$A)
             ==> Reads1#canCall(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0)
               && (Set#Equal(Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0), 
                  Set#Empty(): Set Box)
                 ==> Requires1#canCall(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0)))
         && _module.__default.Total(_module._default.Total$A, _module._default.Total$B, $Heap, f#0)
           == (forall a#0: Box :: 
            { Requires1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0) } 
              { Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0) } 
            $IsBox(a#0, _module._default.Total$A)
               ==> Set#Equal(Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0), 
                  Set#Empty(): Set Box)
                 && Requires1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#0)));

procedure CheckWellformed$$_module.__default.Total(_module._default.Total$A: Ty, 
    _module._default.Total$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.Total$A, _module._default.Total$B)));
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Total(_module._default.Total$A: Ty, _module._default.Total$B: Ty, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _x0#1: Box;
  var _o0#1: ref;
  var a#1: Box;
  var ##x0#0: Box;
  var ##x0#1: Box;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Total
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(71,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (exists _x1#0: Box, _o1#0: ref :: 
          $IsBox(_x1#0, _module._default.Total$A)
             && $Is(_o1#0, Tclass._System.object?())
             && Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, _x1#0)[$Box(_o1#0)]
             && $Box($o) == $Box(_o1#0)));
    assert true;
    // Begin Comprehension WF check
    havoc _x0#1;
    havoc _o0#1;
    if ($IsBox(_x0#1, _module._default.Total$A) && $Is(_o0#1, Tclass._System.object?()))
    {
        assert true;
        assert Requires1(_module._default.Total$A, 
          TSet(Tclass._System.object?()), 
          $Heap, 
          Reads1#Handle(_module._default.Total$A, _module._default.Total$B, f#0), 
          _x0#1);
        if (Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, _x0#1)[$Box(_o0#1)])
        {
        }
    }

    // End Comprehension WF check
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (exists _x2#0: Box, _o2#0: ref :: 
              $IsBox(_x2#0, _module._default.Total$A)
                 && $Is(_o2#0, Tclass._System.object?())
                 && Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, _x2#0)[$Box(_o2#0)]
                 && $Box($o) == $Box(_o2#0)));
        // Begin Comprehension WF check
        havoc a#1;
        if ($IsBox(a#1, _module._default.Total$A))
        {
            ##x0#0 := a#1;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x0#0, _module._default.Total$A, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, ##x0#0)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assume Reads1#canCall(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#1);
            if (Set#Equal(Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#1), 
              Set#Empty(): Set Box))
            {
                ##x0#1 := a#1;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x0#1, _module._default.Total$A, $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
                  $o != null
                       && read($Heap, $o, alloc)
                       && Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, ##x0#1)[$Box($o)]
                     ==> $_Frame[$o, $f]);
                assume Requires1#canCall(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#1);
            }
        }

        // End Comprehension WF check
        assume _module.__default.Total(_module._default.Total$A, _module._default.Total$B, $Heap, f#0)
           == (forall a#2: Box :: 
            { Requires1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2) } 
              { Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2) } 
            $IsBox(a#2, _module._default.Total$A)
               ==> Set#Equal(Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2), 
                  Set#Empty(): Set Box)
                 && Requires1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2));
        assume (forall a#2: Box :: 
          { Requires1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2) } 
            { Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2) } 
          $IsBox(a#2, _module._default.Total$A)
             ==> Reads1#canCall(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2)
               && (Set#Equal(Reads1(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2), 
                  Set#Empty(): Set Box)
                 ==> Requires1#canCall(_module._default.Total$A, _module._default.Total$B, $Heap, f#0, a#2)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Total(_module._default.Total$A, _module._default.Total$B, $Heap, f#0), 
          TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.TotalWitness
function _module.__default.TotalWitness(_module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    a#0: Box)
   : Box;

function _module.__default.TotalWitness#canCall(_module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    a#0: Box)
   : bool;

// consequence axiom for _module.__default.TotalWitness
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.TotalWitness$A: Ty, 
      _module._default.TotalWitness$B: Ty, 
      a#0: Box :: 
    { _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0) } 
    _module.__default.TotalWitness#canCall(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0)
         || (3 != $FunctionContextHeight && $IsBox(a#0, _module._default.TotalWitness$A))
       ==> $IsBox(_module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0), 
        _module._default.TotalWitness$B));

function _module.__default.TotalWitness#requires(Ty, Ty, Box) : bool;

// #requires axiom for _module.__default.TotalWitness
axiom (forall _module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    $Heap: Heap, 
    a#0: Box :: 
  { _module.__default.TotalWitness#requires(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $IsBox(a#0, _module._default.TotalWitness$A)
     ==> _module.__default.TotalWitness#requires(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0)
       == true);

function $let#3_b() : Box;

function $let#3$canCall() : bool;

axiom $let#3$canCall() ==> Lit(true);

// definition axiom for _module.__default.TotalWitness (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.TotalWitness$A: Ty, 
      _module._default.TotalWitness$B: Ty, 
      $Heap: Heap, 
      a#0: Box :: 
    { _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0), $IsGoodHeap($Heap) } 
    _module.__default.TotalWitness#canCall(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0)
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $IsBox(a#0, _module._default.TotalWitness$A))
       ==> $let#3$canCall()
         && _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0)
           == (var b#0 := $let#3_b(); b#0));

// definition axiom for _module.__default.TotalWitness for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.TotalWitness$A: Ty, 
      _module._default.TotalWitness$B: Ty, 
      $Heap: Heap, 
      a#0: Box :: 
    {:weight 3} { _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, Lit(a#0)), $IsGoodHeap($Heap) } 
    _module.__default.TotalWitness#canCall(_module._default.TotalWitness$A, _module._default.TotalWitness$B, Lit(a#0))
         || (3 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $IsBox(a#0, _module._default.TotalWitness$A))
       ==> $let#3$canCall()
         && _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, Lit(a#0))
           == (var b#1 := $let#3_b(); b#1));

procedure CheckWellformed$$_module.__default.TotalWitness(_module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    a#0: Box where $IsBox(a#0, _module._default.TotalWitness$A));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TotalWitness(_module._default.TotalWitness$A: Ty, 
    _module._default.TotalWitness$B: Ty, 
    a#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#2: Box;


    // AddWellformednessCheck for function TotalWitness
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(81,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $IsBox(_module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0), 
          _module._default.TotalWitness$B);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc b#2;
        if ($IsBox(b#2, _module._default.TotalWitness$B))
        {
        }

        assert true;
        assume $IsBox(b#2, _module._default.TotalWitness$B);
        assume true;
        assume $let#3$canCall();
        assume _module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0)
           == b#2;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $IsBox(_module.__default.TotalWitness(_module._default.TotalWitness$A, _module._default.TotalWitness$B, a#0), 
          _module._default.TotalWitness$B);
    }
}



procedure CheckWellformed$$_module.__default.TotalWitnessIsTotal(_module._default.TotalWitnessIsTotal$A: Ty, 
    _module._default.TotalWitnessIsTotal$B: Ty);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TotalWitnessIsTotal(_module._default.TotalWitnessIsTotal$A: Ty, 
    _module._default.TotalWitnessIsTotal$B: Ty)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##f#0: HandleType;

    // AddMethodImpl: TotalWitnessIsTotal, CheckWellformed$$_module.__default.TotalWitnessIsTotal
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(86,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(87,15): post-state"} true;
    assert 3 != $FunctionContextHeight;
    ##f#0 := _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B);
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#0, 
      Tclass._System.___hFunc1(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
      $Heap);
    assume _module.__default.Total#canCall(_module._default.TotalWitnessIsTotal$A, 
      _module._default.TotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B));
    assume _module.__default.Total(_module._default.TotalWitnessIsTotal$A, 
      _module._default.TotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B));
}



procedure Call$$_module.__default.TotalWitnessIsTotal(_module._default.TotalWitnessIsTotal$A: Ty, 
    _module._default.TotalWitnessIsTotal$B: Ty);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Total#canCall(_module._default.TotalWitnessIsTotal$A, 
    _module._default.TotalWitnessIsTotal$B, 
    $Heap, 
    _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B));
  free ensures _module.__default.Total#canCall(_module._default.TotalWitnessIsTotal$A, 
      _module._default.TotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B))
     && 
    _module.__default.Total(_module._default.TotalWitnessIsTotal$A, 
      _module._default.TotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B))
     && (forall a#0: Box :: 
      { Requires1(_module._default.TotalWitnessIsTotal$A, 
          _module._default.TotalWitnessIsTotal$B, 
          $Heap, 
          _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
          a#0) } 
        { Reads1(_module._default.TotalWitnessIsTotal$A, 
          _module._default.TotalWitnessIsTotal$B, 
          $Heap, 
          _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
          a#0) } 
      $IsBox(a#0, _module._default.TotalWitnessIsTotal$A)
         ==> Set#Equal(Reads1(_module._default.TotalWitnessIsTotal$A, 
              _module._default.TotalWitnessIsTotal$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
              a#0), 
            Set#Empty(): Set Box)
           && Requires1(_module._default.TotalWitnessIsTotal$A, 
            _module._default.TotalWitnessIsTotal$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
            a#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.TotalWitnessIsTotal(_module._default.TotalWitnessIsTotal$A: Ty, 
    _module._default.TotalWitnessIsTotal$B: Ty)
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Total#canCall(_module._default.TotalWitnessIsTotal$A, 
    _module._default.TotalWitnessIsTotal$B, 
    $Heap, 
    _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B));
  ensures _module.__default.Total#canCall(_module._default.TotalWitnessIsTotal$A, 
      _module._default.TotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B))
     ==> _module.__default.Total(_module._default.TotalWitnessIsTotal$A, 
        _module._default.TotalWitnessIsTotal$B, 
        $Heap, 
        _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B))
       || (forall a#1: Box :: 
        { Requires1(_module._default.TotalWitnessIsTotal$A, 
            _module._default.TotalWitnessIsTotal$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
            a#1) } 
          { Reads1(_module._default.TotalWitnessIsTotal$A, 
            _module._default.TotalWitnessIsTotal$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
            a#1) } 
        $IsBox(a#1, _module._default.TotalWitnessIsTotal$A)
           ==> Set#Equal(Reads1(_module._default.TotalWitnessIsTotal$A, 
                _module._default.TotalWitnessIsTotal$B, 
                $Heap, 
                _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
                a#1), 
              Set#Empty(): Set Box)
             && Requires1(_module._default.TotalWitnessIsTotal$A, 
              _module._default.TotalWitnessIsTotal$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module._default.TotalWitnessIsTotal$A, _module._default.TotalWitnessIsTotal$B), 
              a#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.TotalWitnessIsTotal(_module._default.TotalWitnessIsTotal$A: Ty, 
    _module._default.TotalWitnessIsTotal$B: Ty)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: TotalWitnessIsTotal, Impl$$_module.__default.TotalWitnessIsTotal
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(88,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.TotalClientTwice
function _module.__default.TotalClientTwice(f#0: HandleType, x#0: int) : int;

function _module.__default.TotalClientTwice#canCall(f#0: HandleType, x#0: int) : bool;

// consequence axiom for _module.__default.TotalClientTwice
axiom 9 <= $FunctionContextHeight
   ==> (forall f#0: HandleType, x#0: int :: 
    { _module.__default.TotalClientTwice(f#0, x#0) } 
    _module.__default.TotalClientTwice#canCall(f#0, x#0)
         || (9 != $FunctionContextHeight && $Is(f#0, Tclass._module.TotalArrow(TInt, TInt)))
       ==> true);

function _module.__default.TotalClientTwice#requires(HandleType, int) : bool;

// #requires axiom for _module.__default.TotalClientTwice
axiom (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
  { _module.__default.TotalClientTwice#requires(f#0, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(f#0, Tclass._module.TotalArrow(TInt, TInt))
     ==> _module.__default.TotalClientTwice#requires(f#0, x#0) == true);

// definition axiom for _module.__default.TotalClientTwice (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.TotalClientTwice(f#0, x#0), $IsGoodHeap($Heap) } 
    _module.__default.TotalClientTwice#canCall(f#0, x#0)
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.TotalArrow(TInt, TInt)))
       ==> _module.__default.TotalClientTwice(f#0, x#0)
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            f#0, 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int);

// definition axiom for _module.__default.TotalClientTwice for decreasing-related literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    {:weight 3} { _module.__default.TotalClientTwice(f#0, LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.__default.TotalClientTwice#canCall(f#0, LitInt(x#0))
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.TotalArrow(TInt, TInt)))
       ==> _module.__default.TotalClientTwice(f#0, LitInt(x#0))
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            f#0, 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(LitInt(x#0)))): int))): int);

// definition axiom for _module.__default.TotalClientTwice for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    {:weight 3} { _module.__default.TotalClientTwice(Lit(f#0), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.__default.TotalClientTwice#canCall(Lit(f#0), LitInt(x#0))
         || (9 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.TotalArrow(TInt, TInt)))
       ==> _module.__default.TotalClientTwice(Lit(f#0), LitInt(x#0))
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            Lit(f#0), 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, Lit(f#0), $Box(LitInt(x#0)))): int))): int);

procedure CheckWellformed$$_module.__default.TotalClientTwice(f#0: HandleType where $Is(f#0, Tclass._module.TotalArrow(TInt, TInt)), x#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TotalClientTwice(f#0: HandleType, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function TotalClientTwice
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(91,9): initial state"} true;
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
        assert Requires1(TInt, TInt, $Heap, f#0, $Box(x#0));
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, TInt, $Heap, f#0, $Box(x#0))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert Requires1(TInt, 
          TInt, 
          $Heap, 
          f#0, 
          $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int));
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, 
                TInt, 
                $Heap, 
                f#0, 
                $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume _module.__default.TotalClientTwice(f#0, x#0)
           == $Unbox(Apply1(TInt, 
              TInt, 
              $Heap, 
              f#0, 
              $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.TotalClientTwice(f#0, x#0), TInt);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.DirectTotalWitnessIsTotal(_module._default.DirectTotalWitnessIsTotal$A: Ty, 
    _module._default.DirectTotalWitnessIsTotal$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
          Tclass._module.DirectTotalArrow(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B))
         && $IsAlloc(f#0, 
          Tclass._module.DirectTotalArrow(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B), 
          $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.DirectTotalWitnessIsTotal(_module._default.DirectTotalWitnessIsTotal$A: Ty, 
    _module._default.DirectTotalWitnessIsTotal$B: Ty, 
    f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##f#0: HandleType;

    // AddMethodImpl: DirectTotalWitnessIsTotal, CheckWellformed$$_module.__default.DirectTotalWitnessIsTotal
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(102,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(103,15): post-state"} true;
    assert 3 != $FunctionContextHeight;
    ##f#0 := _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
      _module._default.DirectTotalWitnessIsTotal$B);
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#0, 
      Tclass._System.___hFunc1(_module._default.DirectTotalWitnessIsTotal$A, 
        _module._default.DirectTotalWitnessIsTotal$B), 
      $Heap);
    assume _module.__default.Total#canCall(_module._default.DirectTotalWitnessIsTotal$A, 
      _module._default.DirectTotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
        _module._default.DirectTotalWitnessIsTotal$B));
    assume _module.__default.Total(_module._default.DirectTotalWitnessIsTotal$A, 
      _module._default.DirectTotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
        _module._default.DirectTotalWitnessIsTotal$B));
}



procedure Call$$_module.__default.DirectTotalWitnessIsTotal(_module._default.DirectTotalWitnessIsTotal$A: Ty, 
    _module._default.DirectTotalWitnessIsTotal$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
          Tclass._module.DirectTotalArrow(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B))
         && $IsAlloc(f#0, 
          Tclass._module.DirectTotalArrow(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B), 
          $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Total#canCall(_module._default.DirectTotalWitnessIsTotal$A, 
    _module._default.DirectTotalWitnessIsTotal$B, 
    $Heap, 
    _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
      _module._default.DirectTotalWitnessIsTotal$B));
  free ensures _module.__default.Total#canCall(_module._default.DirectTotalWitnessIsTotal$A, 
      _module._default.DirectTotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
        _module._default.DirectTotalWitnessIsTotal$B))
     && 
    _module.__default.Total(_module._default.DirectTotalWitnessIsTotal$A, 
      _module._default.DirectTotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
        _module._default.DirectTotalWitnessIsTotal$B))
     && (forall a#0: Box :: 
      { Requires1(_module._default.DirectTotalWitnessIsTotal$A, 
          _module._default.DirectTotalWitnessIsTotal$B, 
          $Heap, 
          _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B), 
          a#0) } 
        { Reads1(_module._default.DirectTotalWitnessIsTotal$A, 
          _module._default.DirectTotalWitnessIsTotal$B, 
          $Heap, 
          _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B), 
          a#0) } 
      $IsBox(a#0, _module._default.DirectTotalWitnessIsTotal$A)
         ==> Set#Equal(Reads1(_module._default.DirectTotalWitnessIsTotal$A, 
              _module._default.DirectTotalWitnessIsTotal$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
                _module._default.DirectTotalWitnessIsTotal$B), 
              a#0), 
            Set#Empty(): Set Box)
           && Requires1(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
              _module._default.DirectTotalWitnessIsTotal$B), 
            a#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.DirectTotalWitnessIsTotal(_module._default.DirectTotalWitnessIsTotal$A: Ty, 
    _module._default.DirectTotalWitnessIsTotal$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
          Tclass._module.DirectTotalArrow(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B))
         && $IsAlloc(f#0, 
          Tclass._module.DirectTotalArrow(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B), 
          $Heap))
   returns ($_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Total#canCall(_module._default.DirectTotalWitnessIsTotal$A, 
    _module._default.DirectTotalWitnessIsTotal$B, 
    $Heap, 
    _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
      _module._default.DirectTotalWitnessIsTotal$B));
  ensures _module.__default.Total#canCall(_module._default.DirectTotalWitnessIsTotal$A, 
      _module._default.DirectTotalWitnessIsTotal$B, 
      $Heap, 
      _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
        _module._default.DirectTotalWitnessIsTotal$B))
     ==> _module.__default.Total(_module._default.DirectTotalWitnessIsTotal$A, 
        _module._default.DirectTotalWitnessIsTotal$B, 
        $Heap, 
        _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
          _module._default.DirectTotalWitnessIsTotal$B))
       || (forall a#1: Box :: 
        { Requires1(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
              _module._default.DirectTotalWitnessIsTotal$B), 
            a#1) } 
          { Reads1(_module._default.DirectTotalWitnessIsTotal$A, 
            _module._default.DirectTotalWitnessIsTotal$B, 
            $Heap, 
            _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
              _module._default.DirectTotalWitnessIsTotal$B), 
            a#1) } 
        $IsBox(a#1, _module._default.DirectTotalWitnessIsTotal$A)
           ==> Set#Equal(Reads1(_module._default.DirectTotalWitnessIsTotal$A, 
                _module._default.DirectTotalWitnessIsTotal$B, 
                $Heap, 
                _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
                  _module._default.DirectTotalWitnessIsTotal$B), 
                a#1), 
              Set#Empty(): Set Box)
             && Requires1(_module._default.DirectTotalWitnessIsTotal$A, 
              _module._default.DirectTotalWitnessIsTotal$B, 
              $Heap, 
              _module.__default.TotalWitness#Handle(_module._default.DirectTotalWitnessIsTotal$A, 
                _module._default.DirectTotalWitnessIsTotal$B), 
              a#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.DirectTotalWitnessIsTotal(_module._default.DirectTotalWitnessIsTotal$A: Ty, 
    _module._default.DirectTotalWitnessIsTotal$B: Ty, 
    f#0: HandleType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: DirectTotalWitnessIsTotal, Impl$$_module.__default.DirectTotalWitnessIsTotal
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(104,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.DirectTotalClientTwice
function _module.__default.DirectTotalClientTwice(f#0: HandleType, x#0: int) : int;

function _module.__default.DirectTotalClientTwice#canCall(f#0: HandleType, x#0: int) : bool;

// consequence axiom for _module.__default.DirectTotalClientTwice
axiom 11 <= $FunctionContextHeight
   ==> (forall f#0: HandleType, x#0: int :: 
    { _module.__default.DirectTotalClientTwice(f#0, x#0) } 
    _module.__default.DirectTotalClientTwice#canCall(f#0, x#0)
         || (11 != $FunctionContextHeight
           && $Is(f#0, Tclass._module.DirectTotalArrow(TInt, TInt)))
       ==> true);

function _module.__default.DirectTotalClientTwice#requires(HandleType, int) : bool;

// #requires axiom for _module.__default.DirectTotalClientTwice
axiom (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
  { _module.__default.DirectTotalClientTwice#requires(f#0, x#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(f#0, Tclass._module.DirectTotalArrow(TInt, TInt))
     ==> _module.__default.DirectTotalClientTwice#requires(f#0, x#0) == true);

// definition axiom for _module.__default.DirectTotalClientTwice (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    { _module.__default.DirectTotalClientTwice(f#0, x#0), $IsGoodHeap($Heap) } 
    _module.__default.DirectTotalClientTwice#canCall(f#0, x#0)
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.DirectTotalArrow(TInt, TInt)))
       ==> _module.__default.DirectTotalClientTwice(f#0, x#0)
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            f#0, 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int);

// definition axiom for _module.__default.DirectTotalClientTwice for decreasing-related literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    {:weight 3} { _module.__default.DirectTotalClientTwice(f#0, LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.__default.DirectTotalClientTwice#canCall(f#0, LitInt(x#0))
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.DirectTotalArrow(TInt, TInt)))
       ==> _module.__default.DirectTotalClientTwice(f#0, LitInt(x#0))
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            f#0, 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(LitInt(x#0)))): int))): int);

// definition axiom for _module.__default.DirectTotalClientTwice for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, f#0: HandleType, x#0: int :: 
    {:weight 3} { _module.__default.DirectTotalClientTwice(Lit(f#0), LitInt(x#0)), $IsGoodHeap($Heap) } 
    _module.__default.DirectTotalClientTwice#canCall(Lit(f#0), LitInt(x#0))
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, Tclass._module.DirectTotalArrow(TInt, TInt)))
       ==> _module.__default.DirectTotalClientTwice(Lit(f#0), LitInt(x#0))
         == $Unbox(Apply1(TInt, 
            TInt, 
            $Heap, 
            Lit(f#0), 
            $Box($Unbox(Apply1(TInt, TInt, $Heap, Lit(f#0), $Box(LitInt(x#0)))): int))): int);

procedure CheckWellformed$$_module.__default.DirectTotalClientTwice(f#0: HandleType where $Is(f#0, Tclass._module.DirectTotalArrow(TInt, TInt)), 
    x#0: int);
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.DirectTotalClientTwice(f#0: HandleType, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function DirectTotalClientTwice
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(107,9): initial state"} true;
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
        assert Requires1(TInt, TInt, $Heap, f#0, $Box(x#0));
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, TInt, $Heap, f#0, $Box(x#0))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assert Requires1(TInt, 
          TInt, 
          $Heap, 
          f#0, 
          $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int));
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && Reads1(TInt, 
                TInt, 
                $Heap, 
                f#0, 
                $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume _module.__default.DirectTotalClientTwice(f#0, x#0)
           == $Unbox(Apply1(TInt, 
              TInt, 
              $Heap, 
              f#0, 
              $Box($Unbox(Apply1(TInt, TInt, $Heap, f#0, $Box(x#0))): int))): int;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.DirectTotalClientTwice(f#0, x#0), TInt);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.EmptyReads
function _module.__default.EmptyReads(_module._default.EmptyReads$A: Ty, 
    _module._default.EmptyReads$B: Ty, 
    $heap: Heap, 
    f#0: HandleType)
   : bool;

function _module.__default.EmptyReads#canCall(_module._default.EmptyReads$A: Ty, 
    _module._default.EmptyReads$B: Ty, 
    $heap: Heap, 
    f#0: HandleType)
   : bool;

// frame axiom for _module.__default.EmptyReads
axiom (forall _module._default.EmptyReads$A: Ty, 
    _module._default.EmptyReads$B: Ty, 
    $h0: Heap, 
    $h1: Heap, 
    f#0: HandleType :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.EmptyReads(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $h1, f#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.EmptyReads#canCall(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $h0, f#0)
         || $Is(f#0, 
          Tclass._System.___hFunc1(_module._default.EmptyReads$A, _module._default.EmptyReads$B)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (exists _x0#0: Box, _o0#0: ref :: 
            $IsBox(_x0#0, _module._default.EmptyReads$A)
               && $Is(_o0#0, Tclass._System.object?())
               && Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $h0, f#0, _x0#0)[$Box(_o0#0)]
               && $Box($o) == $Box(_o0#0))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.EmptyReads(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $h0, f#0)
       == _module.__default.EmptyReads(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $h1, f#0));

// consequence axiom for _module.__default.EmptyReads
axiom 20 <= $FunctionContextHeight
   ==> (forall _module._default.EmptyReads$A: Ty, 
      _module._default.EmptyReads$B: Ty, 
      $Heap: Heap, 
      f#0: HandleType :: 
    { _module.__default.EmptyReads(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0) } 
    _module.__default.EmptyReads#canCall(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0)
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.EmptyReads$A, _module._default.EmptyReads$B)))
       ==> true);

function _module.__default.EmptyReads#requires(Ty, Ty, Heap, HandleType) : bool;

// #requires axiom for _module.__default.EmptyReads
axiom (forall _module._default.EmptyReads$A: Ty, 
    _module._default.EmptyReads$B: Ty, 
    $Heap: Heap, 
    f#0: HandleType :: 
  { _module.__default.EmptyReads#requires(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.EmptyReads$A, _module._default.EmptyReads$B))
     ==> _module.__default.EmptyReads#requires(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0)
       == true);

// definition axiom for _module.__default.EmptyReads (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall _module._default.EmptyReads$A: Ty, 
      _module._default.EmptyReads$B: Ty, 
      $Heap: Heap, 
      f#0: HandleType :: 
    { _module.__default.EmptyReads(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0), $IsGoodHeap($Heap) } 
    _module.__default.EmptyReads#canCall(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0)
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.EmptyReads$A, _module._default.EmptyReads$B)))
       ==> (forall a#0: Box :: 
          { Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#0) } 
          $IsBox(a#0, _module._default.EmptyReads$A)
             ==> Reads1#canCall(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#0))
         && _module.__default.EmptyReads(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0)
           == (forall a#0: Box :: 
            { Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#0) } 
            $IsBox(a#0, _module._default.EmptyReads$A)
               ==> Set#Equal(Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#0), 
                Set#Empty(): Set Box)));

procedure CheckWellformed$$_module.__default.EmptyReads(_module._default.EmptyReads$A: Ty, 
    _module._default.EmptyReads$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.EmptyReads$A, _module._default.EmptyReads$B)));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.EmptyReads(_module._default.EmptyReads$A: Ty, 
    _module._default.EmptyReads$B: Ty, 
    f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _x0#1: Box;
  var _o0#1: ref;
  var a#1: Box;
  var ##x0#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function EmptyReads
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(114,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (exists _x1#0: Box, _o1#0: ref :: 
          $IsBox(_x1#0, _module._default.EmptyReads$A)
             && $Is(_o1#0, Tclass._System.object?())
             && Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, _x1#0)[$Box(_o1#0)]
             && $Box($o) == $Box(_o1#0)));
    assert true;
    // Begin Comprehension WF check
    havoc _x0#1;
    havoc _o0#1;
    if ($IsBox(_x0#1, _module._default.EmptyReads$A)
       && $Is(_o0#1, Tclass._System.object?()))
    {
        assert true;
        assert Requires1(_module._default.EmptyReads$A, 
          TSet(Tclass._System.object?()), 
          $Heap, 
          Reads1#Handle(_module._default.EmptyReads$A, _module._default.EmptyReads$B, f#0), 
          _x0#1);
        if (Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, _x0#1)[$Box(_o0#1)])
        {
        }
    }

    // End Comprehension WF check
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (exists _x2#0: Box, _o2#0: ref :: 
              $IsBox(_x2#0, _module._default.EmptyReads$A)
                 && $Is(_o2#0, Tclass._System.object?())
                 && Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, _x2#0)[$Box(_o2#0)]
                 && $Box($o) == $Box(_o2#0)));
        // Begin Comprehension WF check
        havoc a#1;
        if ($IsBox(a#1, _module._default.EmptyReads$A))
        {
            ##x0#0 := a#1;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x0#0, _module._default.EmptyReads$A, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, ##x0#0)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assume Reads1#canCall(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#1);
        }

        // End Comprehension WF check
        assume _module.__default.EmptyReads(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0)
           == (forall a#2: Box :: 
            { Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#2) } 
            $IsBox(a#2, _module._default.EmptyReads$A)
               ==> Set#Equal(Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#2), 
                Set#Empty(): Set Box));
        assume (forall a#2: Box :: 
          { Reads1(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#2) } 
          $IsBox(a#2, _module._default.EmptyReads$A)
             ==> Reads1#canCall(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0, a#2));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.EmptyReads(_module._default.EmptyReads$A, _module._default.EmptyReads$B, $Heap, f#0), 
          TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.TruePre
function _module.__default.TruePre(_module._default.TruePre$A: Ty, 
    _module._default.TruePre$B: Ty, 
    $heap: Heap, 
    f#0: HandleType)
   : bool;

function _module.__default.TruePre#canCall(_module._default.TruePre$A: Ty, 
    _module._default.TruePre$B: Ty, 
    $heap: Heap, 
    f#0: HandleType)
   : bool;

// frame axiom for _module.__default.TruePre
axiom (forall _module._default.TruePre$A: Ty, 
    _module._default.TruePre$B: Ty, 
    $h0: Heap, 
    $h1: Heap, 
    f#0: HandleType :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.__default.TruePre(_module._default.TruePre$A, _module._default.TruePre$B, $h1, f#0) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && (_module.__default.TruePre#canCall(_module._default.TruePre$A, _module._default.TruePre$B, $h0, f#0)
         || $Is(f#0, 
          Tclass._System.___hFunc1(_module._default.TruePre$A, _module._default.TruePre$B)))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (exists _x0#0: Box, _o0#0: ref :: 
            $IsBox(_x0#0, _module._default.TruePre$A)
               && $Is(_o0#0, Tclass._System.object?())
               && Reads1(_module._default.TruePre$A, _module._default.TruePre$B, $h0, f#0, _x0#0)[$Box(_o0#0)]
               && $Box($o) == $Box(_o0#0))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.__default.TruePre(_module._default.TruePre$A, _module._default.TruePre$B, $h0, f#0)
       == _module.__default.TruePre(_module._default.TruePre$A, _module._default.TruePre$B, $h1, f#0));

// consequence axiom for _module.__default.TruePre
axiom 21 <= $FunctionContextHeight
   ==> (forall _module._default.TruePre$A: Ty, 
      _module._default.TruePre$B: Ty, 
      $Heap: Heap, 
      f#0: HandleType :: 
    { _module.__default.TruePre(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0) } 
    _module.__default.TruePre#canCall(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0)
         || (21 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.TruePre$A, _module._default.TruePre$B)))
       ==> true);

function _module.__default.TruePre#requires(Ty, Ty, Heap, HandleType) : bool;

// #requires axiom for _module.__default.TruePre
axiom (forall _module._default.TruePre$A: Ty, 
    _module._default.TruePre$B: Ty, 
    $Heap: Heap, 
    f#0: HandleType :: 
  { _module.__default.TruePre#requires(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.TruePre$A, _module._default.TruePre$B))
     ==> _module.__default.TruePre#requires(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0)
       == true);

// definition axiom for _module.__default.TruePre (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall _module._default.TruePre$A: Ty, 
      _module._default.TruePre$B: Ty, 
      $Heap: Heap, 
      f#0: HandleType :: 
    { _module.__default.TruePre(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0), $IsGoodHeap($Heap) } 
    _module.__default.TruePre#canCall(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0)
         || (21 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, 
            Tclass._System.___hFunc1(_module._default.TruePre$A, _module._default.TruePre$B)))
       ==> (forall a#0: Box :: 
          { Requires1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#0) } 
          $IsBox(a#0, _module._default.TruePre$A)
             ==> Requires1#canCall(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#0))
         && _module.__default.TruePre(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0)
           == (forall a#0: Box :: 
            { Requires1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#0) } 
            $IsBox(a#0, _module._default.TruePre$A)
               ==> Requires1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#0)));

procedure CheckWellformed$$_module.__default.TruePre(_module._default.TruePre$A: Ty, 
    _module._default.TruePre$B: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hFunc1(_module._default.TruePre$A, _module._default.TruePre$B)));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.TruePre(_module._default.TruePre$A: Ty, _module._default.TruePre$B: Ty, f#0: HandleType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _x0#1: Box;
  var _o0#1: ref;
  var a#1: Box;
  var ##x0#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function TruePre
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(120,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> (exists _x1#0: Box, _o1#0: ref :: 
          $IsBox(_x1#0, _module._default.TruePre$A)
             && $Is(_o1#0, Tclass._System.object?())
             && Reads1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, _x1#0)[$Box(_o1#0)]
             && $Box($o) == $Box(_o1#0)));
    assert true;
    // Begin Comprehension WF check
    havoc _x0#1;
    havoc _o0#1;
    if ($IsBox(_x0#1, _module._default.TruePre$A)
       && $Is(_o0#1, Tclass._System.object?()))
    {
        assert true;
        assert Requires1(_module._default.TruePre$A, 
          TSet(Tclass._System.object?()), 
          $Heap, 
          Reads1#Handle(_module._default.TruePre$A, _module._default.TruePre$B, f#0), 
          _x0#1);
        if (Reads1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, _x0#1)[$Box(_o0#1)])
        {
        }
    }

    // End Comprehension WF check
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc)
             ==> (exists _x2#0: Box, _o2#0: ref :: 
              $IsBox(_x2#0, _module._default.TruePre$A)
                 && $Is(_o2#0, Tclass._System.object?())
                 && Reads1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, _x2#0)[$Box(_o2#0)]
                 && $Box($o) == $Box(_o2#0)));
        // Begin Comprehension WF check
        havoc a#1;
        if ($IsBox(a#1, _module._default.TruePre$A))
        {
            ##x0#0 := a#1;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x0#0, _module._default.TruePre$A, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: 
              $o != null
                   && read($Heap, $o, alloc)
                   && Reads1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, ##x0#0)[$Box($o)]
                 ==> $_Frame[$o, $f]);
            assume Requires1#canCall(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#1);
        }

        // End Comprehension WF check
        assume _module.__default.TruePre(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0)
           == (forall a#2: Box :: 
            { Requires1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#2) } 
            $IsBox(a#2, _module._default.TruePre$A)
               ==> Requires1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#2));
        assume (forall a#2: Box :: 
          { Requires1(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#2) } 
          $IsBox(a#2, _module._default.TruePre$A)
             ==> Requires1#canCall(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0, a#2));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.TruePre(_module._default.TruePre$A, _module._default.TruePre$B, $Heap, f#0), 
          TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.SomeCondition
function _module.__default.SomeCondition(_module._default.SomeCondition$A: Ty, a#0: Box) : bool;

function _module.__default.SomeCondition#canCall(_module._default.SomeCondition$A: Ty, a#0: Box) : bool;

// consequence axiom for _module.__default.SomeCondition
axiom 23 <= $FunctionContextHeight
   ==> (forall _module._default.SomeCondition$A: Ty, a#0: Box :: 
    { _module.__default.SomeCondition(_module._default.SomeCondition$A, a#0) } 
    _module.__default.SomeCondition#canCall(_module._default.SomeCondition$A, a#0)
         || (23 != $FunctionContextHeight && $IsBox(a#0, _module._default.SomeCondition$A))
       ==> true);

function _module.__default.SomeCondition#requires(Ty, Box) : bool;

// #requires axiom for _module.__default.SomeCondition
axiom (forall _module._default.SomeCondition$A: Ty, a#0: Box :: 
  { _module.__default.SomeCondition#requires(_module._default.SomeCondition$A, a#0) } 
  $IsBox(a#0, _module._default.SomeCondition$A)
     ==> _module.__default.SomeCondition#requires(_module._default.SomeCondition$A, a#0)
       == true);

procedure CheckWellformed$$_module.__default.SomeCondition(_module._default.SomeCondition$A: Ty, 
    a#0: Box where $IsBox(a#0, _module._default.SomeCondition$A));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.PartialFunction
function _module.__default.PartialFunction(_module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    a#0: Box)
   : Box;

function _module.__default.PartialFunction#canCall(_module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    a#0: Box)
   : bool;

// consequence axiom for _module.__default.PartialFunction
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.PartialFunction$A: Ty, 
      _module._default.PartialFunction$B: Ty, 
      a#0: Box :: 
    { _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0) } 
    _module.__default.PartialFunction#canCall(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0)
         || (24 != $FunctionContextHeight
           && 
          $IsBox(a#0, _module._default.PartialFunction$A)
           && _module.__default.SomeCondition(_module._default.PartialFunction$A, a#0))
       ==> $IsBox(_module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0), 
        _module._default.PartialFunction$B));

function _module.__default.PartialFunction#requires(Ty, Ty, Box) : bool;

// #requires axiom for _module.__default.PartialFunction
axiom (forall _module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    $Heap: Heap, 
    a#0: Box :: 
  { _module.__default.PartialFunction#requires(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $IsBox(a#0, _module._default.PartialFunction$A)
     ==> _module.__default.PartialFunction#requires(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0)
       == _module.__default.SomeCondition(_module._default.PartialFunction$A, a#0));

function $let#6_b() : Box;

function $let#6$canCall() : bool;

axiom $let#6$canCall() ==> Lit(true);

// definition axiom for _module.__default.PartialFunction (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.PartialFunction$A: Ty, 
      _module._default.PartialFunction$B: Ty, 
      $Heap: Heap, 
      a#0: Box :: 
    { _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0), $IsGoodHeap($Heap) } 
    _module.__default.PartialFunction#canCall(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0)
         || (24 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $IsBox(a#0, _module._default.PartialFunction$A)
           && _module.__default.SomeCondition(_module._default.PartialFunction$A, a#0))
       ==> $let#6$canCall()
         && _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0)
           == (var b#0 := $let#6_b(); b#0));

// definition axiom for _module.__default.PartialFunction for all literals (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.PartialFunction$A: Ty, 
      _module._default.PartialFunction$B: Ty, 
      $Heap: Heap, 
      a#0: Box :: 
    {:weight 3} { _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, Lit(a#0)), $IsGoodHeap($Heap) } 
    _module.__default.PartialFunction#canCall(_module._default.PartialFunction$A, _module._default.PartialFunction$B, Lit(a#0))
         || (24 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $IsBox(a#0, _module._default.PartialFunction$A)
           && _module.__default.SomeCondition(_module._default.PartialFunction$A, Lit(a#0)))
       ==> $let#6$canCall()
         && _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, Lit(a#0))
           == (var b#1 := $let#6_b(); b#1));

procedure CheckWellformed$$_module.__default.PartialFunction(_module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    a#0: Box where $IsBox(a#0, _module._default.PartialFunction$A));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.PartialFunction(_module._default.PartialFunction$A: Ty, 
    _module._default.PartialFunction$B: Ty, 
    a#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: Box;
  var b$reqreads#0: bool;
  var b#2: Box;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function PartialFunction
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(132,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##a#0, _module._default.PartialFunction$A, $Heap);
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.SomeCondition#canCall(_module._default.PartialFunction$A, a#0);
    assume _module.__default.SomeCondition(_module._default.PartialFunction$A, a#0);
    assert b$reqreads#0;
    if (*)
    {
        assume $IsBox(_module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0), 
          _module._default.PartialFunction$B);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc b#2;
        if ($IsBox(b#2, _module._default.PartialFunction$B))
        {
        }

        assert true;
        assume $IsBox(b#2, _module._default.PartialFunction$B);
        assume true;
        assume $let#6$canCall();
        assume _module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0)
           == b#2;
        assume true;
        // CheckWellformedWithResult: Let expression
        assume $IsBox(_module.__default.PartialFunction(_module._default.PartialFunction$A, _module._default.PartialFunction$B, a#0), 
          _module._default.PartialFunction$B);
    }
}



procedure CheckWellformed$$_module.__default.Any__to__Partial(f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap))
   returns (g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Any__to__Partial(f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap))
   returns (g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap));
  // user-defined preconditions
  requires (forall x#1: int :: 
    { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    true
       ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Any__to__Partial(f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap))
   returns (g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall x#1: int :: 
    { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    true
       ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Any__to__Partial(f#0: HandleType) returns (g#0: HandleType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Any_to_Partial, Impl$$_module.__default.Any__to__Partial
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(147,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(148,5)
    assume true;
    assume true;
    assert $Is(f#0, Tclass._System.___hPartialFunc1(TInt, TInt));
    g#0 := f#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(148,8)"} true;
}



procedure CheckWellformed$$_module.__default.Partial__to__Any(g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap))
   returns (f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Partial__to__Any(g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap))
   returns (f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: int :: 
    { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    Reads1#canCall(TInt, TInt, $Heap, f#0, $Box(x#1)));
  ensures (forall x#1: int :: 
    { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    true
       ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Partial__to__Any(g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap))
   returns (f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: int :: 
    { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    Reads1#canCall(TInt, TInt, $Heap, f#0, $Box(x#1)));
  ensures (forall x#1: int :: 
    { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    true
       ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Partial__to__Any(g#0: HandleType) returns (f#0: HandleType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Partial_to_Any, Impl$$_module.__default.Partial__to__Any
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(153,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(154,5)
    assume true;
    assume true;
    f#0 := g#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(154,8)"} true;
}



procedure CheckWellformed$$_module.__default.Partial__to__Total(g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap))
   returns (tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Partial__to__Total(g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap))
   returns (tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap));
  // user-defined preconditions
  requires (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)) } 
    true ==> Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Partial__to__Total(g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap))
   returns (tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)) } 
    true ==> Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Partial__to__Total(g#0: HandleType) returns (tot#0: HandleType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Partial_to_Total, Impl$$_module.__default.Partial__to__Total
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(159,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(160,7)
    assume true;
    assume true;
    assert $Is(g#0, Tclass._System.___hTotalFunc1(TInt, TInt));
    tot#0 := g#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(160,10)"} true;
}



procedure CheckWellformed$$_module.__default.Total__to__Partial(tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap))
   returns (g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Total__to__Partial(tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap))
   returns (g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)) } 
    Requires1#canCall(TInt, TInt, $Heap, g#0, $Box(x#1)));
  ensures (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)) } 
    true ==> Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Total__to__Partial(tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap))
   returns (g#0: HandleType
       where $Is(g#0, Tclass._System.___hPartialFunc1(TInt, TInt))
         && $IsAlloc(g#0, Tclass._System.___hPartialFunc1(TInt, TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)) } 
    Requires1#canCall(TInt, TInt, $Heap, g#0, $Box(x#1)));
  ensures (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)) } 
    true ==> Requires1(TInt, TInt, $Heap, g#0, $Box(x#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Total__to__Partial(tot#0: HandleType) returns (g#0: HandleType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Total_to_Partial, Impl$$_module.__default.Total__to__Partial
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(165,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(166,5)
    assume true;
    assume true;
    g#0 := tot#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(166,10)"} true;
}



procedure CheckWellformed$$_module.__default.Any__to__Total(f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap))
   returns (tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Any__to__Total(f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap))
   returns (tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap));
  // user-defined preconditions
  requires (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
      { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    true
       ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box)
         && Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Any__to__Total(f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap))
   returns (tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
      { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    true
       ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box)
         && Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Any__to__Total(f#0: HandleType) returns (tot#0: HandleType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Any_to_Total, Impl$$_module.__default.Any__to__Total
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(172,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(173,7)
    assume true;
    assume true;
    assert $Is(f#0, Tclass._System.___hTotalFunc1(TInt, TInt));
    tot#0 := f#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(173,10)"} true;
}



procedure CheckWellformed$$_module.__default.Total__to__Any(tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap))
   returns (f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Total__to__Any(tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap))
   returns (f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
      { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    Reads1#canCall(TInt, TInt, $Heap, f#0, $Box(x#1))
       && (Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box)
         ==> Requires1#canCall(TInt, TInt, $Heap, f#0, $Box(x#1))));
  ensures (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
      { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    true
       ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box)
         && Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Total__to__Any(tot#0: HandleType
       where $Is(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt))
         && $IsAlloc(tot#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap))
   returns (f#0: HandleType
       where $Is(f#0, Tclass._System.___hFunc1(TInt, TInt))
         && $IsAlloc(f#0, Tclass._System.___hFunc1(TInt, TInt), $Heap), 
    $_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
      { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    Reads1#canCall(TInt, TInt, $Heap, f#0, $Box(x#1))
       && (Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box)
         ==> Requires1#canCall(TInt, TInt, $Heap, f#0, $Box(x#1))));
  ensures (forall x#1: int :: 
    { Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
      { Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)) } 
    true
       ==> Set#Equal(Reads1(TInt, TInt, $Heap, f#0, $Box(x#1)), Set#Empty(): Set Box)
         && Requires1(TInt, TInt, $Heap, f#0, $Box(x#1)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Total__to__Any(tot#0: HandleType) returns (f#0: HandleType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Total_to_Any, Impl$$_module.__default.Total__to__Any
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(178,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(179,5)
    assume true;
    assume true;
    f#0 := tot#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/RollYourOwnArrowType.dfy(179,10)"} true;
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

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$NoWitness_EffectlessArrow: TyTagFamily;

const unique tytagFamily$NonGhost_EffectlessArrow: TyTagFamily;

const unique tytagFamily$EffectlessArrow: TyTagFamily;

const unique tytagFamily$TotalArrow: TyTagFamily;

const unique tytagFamily$DirectTotalArrow: TyTagFamily;

const unique tytagFamily$TwoPred_TotalArrow: TyTagFamily;

const unique tytagFamily$Bad_TwoPred_TotalArrow: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
