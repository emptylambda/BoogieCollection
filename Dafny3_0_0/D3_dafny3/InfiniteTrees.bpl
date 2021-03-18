// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy -print:./InfiniteTrees.bpl

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

// Constructor function declaration
function #_module.Tree.Node(DatatypeType) : DatatypeType;

const unique ##_module.Tree.Node: DtCtorId;

// Constructor identifier
axiom (forall a#24#0#0: DatatypeType :: 
  { #_module.Tree.Node(a#24#0#0) } 
  DatatypeCtorId(#_module.Tree.Node(a#24#0#0)) == ##_module.Tree.Node);

function _module.Tree.Node_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d) } 
  _module.Tree.Node_q(d) <==> DatatypeCtorId(d) == ##_module.Tree.Node);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d) } 
  _module.Tree.Node_q(d)
     ==> (exists a#25#0#0: DatatypeType :: d == #_module.Tree.Node(a#25#0#0)));

function Tclass._module.Tree() : Ty;

const unique Tagclass._module.Tree: TyTag;

// Tclass._module.Tree Tag
axiom Tag(Tclass._module.Tree()) == Tagclass._module.Tree
   && TagFamily(Tclass._module.Tree()) == tytagFamily$Tree;

// Box/unbox axiom for Tclass._module.Tree
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Tree()) } 
  $IsBox(bx, Tclass._module.Tree())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Tree()));

// Constructor $Is
axiom (forall a#26#0#0: DatatypeType :: 
  { $Is(#_module.Tree.Node(a#26#0#0), Tclass._module.Tree()) } 
  $Is(#_module.Tree.Node(a#26#0#0), Tclass._module.Tree())
     <==> $Is(a#26#0#0, Tclass._module.Stream(Tclass._module.Tree())));

// Constructor $IsAlloc
axiom (forall a#27#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Tree.Node(a#27#0#0), Tclass._module.Tree(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Tree.Node(a#27#0#0), Tclass._module.Tree(), $h)
       <==> $IsAlloc(a#27#0#0, Tclass._module.Stream(Tclass._module.Tree()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Tree.children(d), Tclass._module.Stream(Tclass._module.Tree()), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Tree.Node_q(d)
       && $IsAlloc(d, Tclass._module.Tree(), $h)
     ==> $IsAlloc(_module.Tree.children(d), Tclass._module.Stream(Tclass._module.Tree()), $h));

// Constructor literal
axiom (forall a#28#0#0: DatatypeType :: 
  { #_module.Tree.Node(Lit(a#28#0#0)) } 
  #_module.Tree.Node(Lit(a#28#0#0)) == Lit(#_module.Tree.Node(a#28#0#0)));

function _module.Tree.children(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#29#0#0: DatatypeType :: 
  { #_module.Tree.Node(a#29#0#0) } 
  _module.Tree.children(#_module.Tree.Node(a#29#0#0)) == a#29#0#0);

// Inductive rank
axiom (forall a#30#0#0: DatatypeType :: 
  { #_module.Tree.Node(a#30#0#0) } 
  DtRank(a#30#0#0) < DtRank(#_module.Tree.Node(a#30#0#0)));

// Depth-one case-split function
function $IsA#_module.Tree(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Tree(d) } 
  $IsA#_module.Tree(d) ==> _module.Tree.Node_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Tree.Node_q(d), $Is(d, Tclass._module.Tree()) } 
  $Is(d, Tclass._module.Tree()) ==> _module.Tree.Node_q(d));

// Datatype extensional equality declaration
function _module.Tree#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Tree.Node
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tree#Equal(a, b) } 
  true
     ==> (_module.Tree#Equal(a, b)
       <==> _module.Tree.children(a) == _module.Tree.children(b)));

// Datatype extensionality axiom: _module.Tree
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Tree#Equal(a, b) } 
  _module.Tree#Equal(a, b) <==> a == b);

const unique class._module.Tree: ClassName;

// Constructor function declaration
function #_module.CoOption.None() : DatatypeType;

const unique ##_module.CoOption.None: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.CoOption.None()) == ##_module.CoOption.None;

function _module.CoOption.None_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.CoOption.None_q(d) } 
  _module.CoOption.None_q(d) <==> DatatypeCtorId(d) == ##_module.CoOption.None);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.CoOption.None_q(d) } 
  _module.CoOption.None_q(d) ==> d == #_module.CoOption.None());

function Tclass._module.CoOption(Ty) : Ty;

const unique Tagclass._module.CoOption: TyTag;

// Tclass._module.CoOption Tag
axiom (forall _module.CoOption$T: Ty :: 
  { Tclass._module.CoOption(_module.CoOption$T) } 
  Tag(Tclass._module.CoOption(_module.CoOption$T)) == Tagclass._module.CoOption
     && TagFamily(Tclass._module.CoOption(_module.CoOption$T)) == tytagFamily$CoOption);

// Tclass._module.CoOption injectivity 0
axiom (forall _module.CoOption$T: Ty :: 
  { Tclass._module.CoOption(_module.CoOption$T) } 
  Tclass._module.CoOption_0(Tclass._module.CoOption(_module.CoOption$T))
     == _module.CoOption$T);

function Tclass._module.CoOption_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.CoOption
axiom (forall _module.CoOption$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.CoOption(_module.CoOption$T)) } 
  $IsBox(bx, Tclass._module.CoOption(_module.CoOption$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.CoOption(_module.CoOption$T)));

// Constructor $Is
axiom (forall _module.CoOption$T: Ty :: 
  { $Is(#_module.CoOption.None(), Tclass._module.CoOption(_module.CoOption$T)) } 
  $Is(#_module.CoOption.None(), Tclass._module.CoOption(_module.CoOption$T)));

// Constructor $IsAlloc
axiom (forall _module.CoOption$T: Ty, $h: Heap :: 
  { $IsAlloc(#_module.CoOption.None(), Tclass._module.CoOption(_module.CoOption$T), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.CoOption.None(), Tclass._module.CoOption(_module.CoOption$T), $h));

// Constructor function declaration
function #_module.CoOption.Some(Box) : DatatypeType;

const unique ##_module.CoOption.Some: DtCtorId;

// Constructor identifier
axiom (forall a#35#0#0: Box :: 
  { #_module.CoOption.Some(a#35#0#0) } 
  DatatypeCtorId(#_module.CoOption.Some(a#35#0#0)) == ##_module.CoOption.Some);

function _module.CoOption.Some_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.CoOption.Some_q(d) } 
  _module.CoOption.Some_q(d) <==> DatatypeCtorId(d) == ##_module.CoOption.Some);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.CoOption.Some_q(d) } 
  _module.CoOption.Some_q(d)
     ==> (exists a#36#0#0: Box :: d == #_module.CoOption.Some(a#36#0#0)));

// Constructor $Is
axiom (forall _module.CoOption$T: Ty, a#37#0#0: Box :: 
  { $Is(#_module.CoOption.Some(a#37#0#0), Tclass._module.CoOption(_module.CoOption$T)) } 
  $Is(#_module.CoOption.Some(a#37#0#0), Tclass._module.CoOption(_module.CoOption$T))
     <==> $IsBox(a#37#0#0, _module.CoOption$T));

// Constructor $IsAlloc
axiom (forall _module.CoOption$T: Ty, a#38#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.CoOption.Some(a#38#0#0), 
      Tclass._module.CoOption(_module.CoOption$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.CoOption.Some(a#38#0#0), 
        Tclass._module.CoOption(_module.CoOption$T), 
        $h)
       <==> $IsAllocBox(a#38#0#0, _module.CoOption$T, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.CoOption$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.CoOption.get(d), _module.CoOption$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.CoOption.Some_q(d)
       && $IsAlloc(d, Tclass._module.CoOption(_module.CoOption$T), $h)
     ==> $IsAllocBox(_module.CoOption.get(d), _module.CoOption$T, $h));

function _module.CoOption.get(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#39#0#0: Box :: 
  { #_module.CoOption.Some(a#39#0#0) } 
  _module.CoOption.get(#_module.CoOption.Some(a#39#0#0)) == a#39#0#0);

// Depth-one case-split function
function $IsA#_module.CoOption(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.CoOption(d) } 
  $IsA#_module.CoOption(d)
     ==> _module.CoOption.None_q(d) || _module.CoOption.Some_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.CoOption$T: Ty, d: DatatypeType :: 
  { _module.CoOption.Some_q(d), $Is(d, Tclass._module.CoOption(_module.CoOption$T)) } 
    { _module.CoOption.None_q(d), $Is(d, Tclass._module.CoOption(_module.CoOption$T)) } 
  $Is(d, Tclass._module.CoOption(_module.CoOption$T))
     ==> _module.CoOption.None_q(d) || _module.CoOption.Some_q(d));

function $Eq#_module.CoOption(Ty, Ty, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.CoOption(_module.CoOption$T#l))
       && $Is(d1, Tclass._module.CoOption(_module.CoOption$T#r))
     ==> ($Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1)
       <==> (_module.CoOption.None_q(d0) && _module.CoOption.None_q(d1))
         || (
          _module.CoOption.Some_q(d0)
           && _module.CoOption.Some_q(d1)
           && (_module.CoOption.Some_q(d0) && _module.CoOption.Some_q(d1)
             ==> _module.CoOption.get(d0) == _module.CoOption.get(d1)))));

// Unbump layer co-equality axiom
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1)
     <==> $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, ly, d0, d1));

// Equality for codatatypes
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1)
     <==> d0 == d1);

function $PrefixEq#_module.CoOption(Ty, Ty, Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.CoOption(_module.CoOption$T#l))
       && $Is(d1, Tclass._module.CoOption(_module.CoOption$T#r))
     ==> ($PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (_module.CoOption.None_q(d0) && _module.CoOption.None_q(d1))
             || (
              _module.CoOption.Some_q(d0)
               && _module.CoOption.Some_q(d1)
               && (_module.CoOption.Some_q(d0) && _module.CoOption.Some_q(d1)
                 ==> _module.CoOption.get(d0) == _module.CoOption.get(d1))))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k)
           ==> $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1) } 
  $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k
         ==> $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, $LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType, 
    m: Box :: 
  { $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1), $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, m, $LS(ly), d0, d1) } 
  ORD#Less(k, m)
       && $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall _module.CoOption$T#l: Ty, 
    _module.CoOption$T#r: Ty, 
    k: Box, 
    ly: LayerType, 
    d0: DatatypeType, 
    d1: DatatypeType :: 
  { $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1) } 
  d0 == d1
     ==> $PrefixEq#_module.CoOption(_module.CoOption$T#l, _module.CoOption$T#r, k, $LS(ly), d0, d1));

const unique class._module.CoOption: ClassName;

// Constructor function declaration
function #_module.Number.Succ(DatatypeType) : DatatypeType;

const unique ##_module.Number.Succ: DtCtorId;

// Constructor identifier
axiom (forall a#40#0#0: DatatypeType :: 
  { #_module.Number.Succ(a#40#0#0) } 
  DatatypeCtorId(#_module.Number.Succ(a#40#0#0)) == ##_module.Number.Succ);

function _module.Number.Succ_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Number.Succ_q(d) } 
  _module.Number.Succ_q(d) <==> DatatypeCtorId(d) == ##_module.Number.Succ);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Number.Succ_q(d) } 
  _module.Number.Succ_q(d)
     ==> (exists a#41#0#0: DatatypeType :: d == #_module.Number.Succ(a#41#0#0)));

function Tclass._module.Number() : Ty;

const unique Tagclass._module.Number: TyTag;

// Tclass._module.Number Tag
axiom Tag(Tclass._module.Number()) == Tagclass._module.Number
   && TagFamily(Tclass._module.Number()) == tytagFamily$Number;

// Box/unbox axiom for Tclass._module.Number
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Number()) } 
  $IsBox(bx, Tclass._module.Number())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Number()));

// Constructor $Is
axiom (forall a#42#0#0: DatatypeType :: 
  { $Is(#_module.Number.Succ(a#42#0#0), Tclass._module.Number()) } 
  $Is(#_module.Number.Succ(a#42#0#0), Tclass._module.Number())
     <==> $Is(a#42#0#0, Tclass._module.Number()));

// Constructor $IsAlloc
axiom (forall a#43#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Number.Succ(a#43#0#0), Tclass._module.Number(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Number.Succ(a#43#0#0), Tclass._module.Number(), $h)
       <==> $IsAlloc(a#43#0#0, Tclass._module.Number(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Number._h4(d), Tclass._module.Number(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Number.Succ_q(d)
       && $IsAlloc(d, Tclass._module.Number(), $h)
     ==> $IsAlloc(_module.Number._h4(d), Tclass._module.Number(), $h));

// Constructor literal
axiom (forall a#44#0#0: DatatypeType :: 
  { #_module.Number.Succ(Lit(a#44#0#0)) } 
  #_module.Number.Succ(Lit(a#44#0#0)) == Lit(#_module.Number.Succ(a#44#0#0)));

function _module.Number._h4(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#45#0#0: DatatypeType :: 
  { #_module.Number.Succ(a#45#0#0) } 
  _module.Number._h4(#_module.Number.Succ(a#45#0#0)) == a#45#0#0);

// Inductive rank
axiom (forall a#46#0#0: DatatypeType :: 
  { #_module.Number.Succ(a#46#0#0) } 
  DtRank(a#46#0#0) < DtRank(#_module.Number.Succ(a#46#0#0)));

// Constructor function declaration
function #_module.Number.Zero(DatatypeType) : DatatypeType;

const unique ##_module.Number.Zero: DtCtorId;

// Constructor identifier
axiom (forall a#47#0#0: DatatypeType :: 
  { #_module.Number.Zero(a#47#0#0) } 
  DatatypeCtorId(#_module.Number.Zero(a#47#0#0)) == ##_module.Number.Zero);

function _module.Number.Zero_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Number.Zero_q(d) } 
  _module.Number.Zero_q(d) <==> DatatypeCtorId(d) == ##_module.Number.Zero);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Number.Zero_q(d) } 
  _module.Number.Zero_q(d)
     ==> (exists a#48#0#0: DatatypeType :: d == #_module.Number.Zero(a#48#0#0)));

// Constructor $Is
axiom (forall a#49#0#0: DatatypeType :: 
  { $Is(#_module.Number.Zero(a#49#0#0), Tclass._module.Number()) } 
  $Is(#_module.Number.Zero(a#49#0#0), Tclass._module.Number())
     <==> $Is(a#49#0#0, Tclass._module.CoOption(Tclass._module.Number())));

// Constructor $IsAlloc
axiom (forall a#50#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Number.Zero(a#50#0#0), Tclass._module.Number(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Number.Zero(a#50#0#0), Tclass._module.Number(), $h)
       <==> $IsAlloc(a#50#0#0, Tclass._module.CoOption(Tclass._module.Number()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.Number._h5(d), Tclass._module.CoOption(Tclass._module.Number()), $h) } 
  $IsGoodHeap($h)
       && 
      _module.Number.Zero_q(d)
       && $IsAlloc(d, Tclass._module.Number(), $h)
     ==> $IsAlloc(_module.Number._h5(d), Tclass._module.CoOption(Tclass._module.Number()), $h));

// Constructor literal
axiom (forall a#51#0#0: DatatypeType :: 
  { #_module.Number.Zero(Lit(a#51#0#0)) } 
  #_module.Number.Zero(Lit(a#51#0#0)) == Lit(#_module.Number.Zero(a#51#0#0)));

function _module.Number._h5(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#52#0#0: DatatypeType :: 
  { #_module.Number.Zero(a#52#0#0) } 
  _module.Number._h5(#_module.Number.Zero(a#52#0#0)) == a#52#0#0);

// Inductive rank
axiom (forall a#53#0#0: DatatypeType :: 
  { #_module.Number.Zero(a#53#0#0) } 
  DtRank(a#53#0#0) < DtRank(#_module.Number.Zero(a#53#0#0)));

// Depth-one case-split function
function $IsA#_module.Number(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Number(d) } 
  $IsA#_module.Number(d) ==> _module.Number.Succ_q(d) || _module.Number.Zero_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.Number.Zero_q(d), $Is(d, Tclass._module.Number()) } 
    { _module.Number.Succ_q(d), $Is(d, Tclass._module.Number()) } 
  $Is(d, Tclass._module.Number())
     ==> _module.Number.Succ_q(d) || _module.Number.Zero_q(d));

// Datatype extensional equality declaration
function _module.Number#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Number.Succ
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Number#Equal(a, b), _module.Number.Succ_q(a) } 
    { _module.Number#Equal(a, b), _module.Number.Succ_q(b) } 
  _module.Number.Succ_q(a) && _module.Number.Succ_q(b)
     ==> (_module.Number#Equal(a, b)
       <==> _module.Number#Equal(_module.Number._h4(a), _module.Number._h4(b))));

// Datatype extensional equality definition: #_module.Number.Zero
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Number#Equal(a, b), _module.Number.Zero_q(a) } 
    { _module.Number#Equal(a, b), _module.Number.Zero_q(b) } 
  _module.Number.Zero_q(a) && _module.Number.Zero_q(b)
     ==> (_module.Number#Equal(a, b) <==> _module.Number._h5(a) == _module.Number._h5(b)));

// Datatype extensionality axiom: _module.Number
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Number#Equal(a, b) } 
  _module.Number#Equal(a, b) <==> a == b);

const unique class._module.Number: ClassName;

// Constructor function declaration
function #_module.InfPath.Right(DatatypeType) : DatatypeType;

const unique ##_module.InfPath.Right: DtCtorId;

// Constructor identifier
axiom (forall a#54#0#0: DatatypeType :: 
  { #_module.InfPath.Right(a#54#0#0) } 
  DatatypeCtorId(#_module.InfPath.Right(a#54#0#0)) == ##_module.InfPath.Right);

function _module.InfPath.Right_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.InfPath.Right_q(d) } 
  _module.InfPath.Right_q(d) <==> DatatypeCtorId(d) == ##_module.InfPath.Right);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.InfPath.Right_q(d) } 
  _module.InfPath.Right_q(d)
     ==> (exists a#55#0#0: DatatypeType :: d == #_module.InfPath.Right(a#55#0#0)));

function Tclass._module.InfPath() : Ty;

const unique Tagclass._module.InfPath: TyTag;

// Tclass._module.InfPath Tag
axiom Tag(Tclass._module.InfPath()) == Tagclass._module.InfPath
   && TagFamily(Tclass._module.InfPath()) == tytagFamily$InfPath;

// Box/unbox axiom for Tclass._module.InfPath
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.InfPath()) } 
  $IsBox(bx, Tclass._module.InfPath())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.InfPath()));

// Constructor $Is
axiom (forall a#56#0#0: DatatypeType :: 
  { $Is(#_module.InfPath.Right(a#56#0#0), Tclass._module.InfPath()) } 
  $Is(#_module.InfPath.Right(a#56#0#0), Tclass._module.InfPath())
     <==> $Is(a#56#0#0, Tclass._module.InfPath()));

// Constructor $IsAlloc
axiom (forall a#57#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.InfPath.Right(a#57#0#0), Tclass._module.InfPath(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.InfPath.Right(a#57#0#0), Tclass._module.InfPath(), $h)
       <==> $IsAlloc(a#57#0#0, Tclass._module.InfPath(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.InfPath._h6(d), Tclass._module.InfPath(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.InfPath.Right_q(d)
       && $IsAlloc(d, Tclass._module.InfPath(), $h)
     ==> $IsAlloc(_module.InfPath._h6(d), Tclass._module.InfPath(), $h));

function _module.InfPath._h6(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#58#0#0: DatatypeType :: 
  { #_module.InfPath.Right(a#58#0#0) } 
  _module.InfPath._h6(#_module.InfPath.Right(a#58#0#0)) == a#58#0#0);

// Constructor function declaration
function #_module.InfPath.Down(DatatypeType) : DatatypeType;

const unique ##_module.InfPath.Down: DtCtorId;

// Constructor identifier
axiom (forall a#59#0#0: DatatypeType :: 
  { #_module.InfPath.Down(a#59#0#0) } 
  DatatypeCtorId(#_module.InfPath.Down(a#59#0#0)) == ##_module.InfPath.Down);

function _module.InfPath.Down_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.InfPath.Down_q(d) } 
  _module.InfPath.Down_q(d) <==> DatatypeCtorId(d) == ##_module.InfPath.Down);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.InfPath.Down_q(d) } 
  _module.InfPath.Down_q(d)
     ==> (exists a#60#0#0: DatatypeType :: d == #_module.InfPath.Down(a#60#0#0)));

// Constructor $Is
axiom (forall a#61#0#0: DatatypeType :: 
  { $Is(#_module.InfPath.Down(a#61#0#0), Tclass._module.InfPath()) } 
  $Is(#_module.InfPath.Down(a#61#0#0), Tclass._module.InfPath())
     <==> $Is(a#61#0#0, Tclass._module.InfPath()));

// Constructor $IsAlloc
axiom (forall a#62#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.InfPath.Down(a#62#0#0), Tclass._module.InfPath(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.InfPath.Down(a#62#0#0), Tclass._module.InfPath(), $h)
       <==> $IsAlloc(a#62#0#0, Tclass._module.InfPath(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.InfPath._h7(d), Tclass._module.InfPath(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.InfPath.Down_q(d)
       && $IsAlloc(d, Tclass._module.InfPath(), $h)
     ==> $IsAlloc(_module.InfPath._h7(d), Tclass._module.InfPath(), $h));

function _module.InfPath._h7(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#63#0#0: DatatypeType :: 
  { #_module.InfPath.Down(a#63#0#0) } 
  _module.InfPath._h7(#_module.InfPath.Down(a#63#0#0)) == a#63#0#0);

// Constructor function declaration
function #_module.InfPath.Stop() : DatatypeType;

const unique ##_module.InfPath.Stop: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.InfPath.Stop()) == ##_module.InfPath.Stop;

function _module.InfPath.Stop_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.InfPath.Stop_q(d) } 
  _module.InfPath.Stop_q(d) <==> DatatypeCtorId(d) == ##_module.InfPath.Stop);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.InfPath.Stop_q(d) } 
  _module.InfPath.Stop_q(d) ==> d == #_module.InfPath.Stop());

// Constructor $Is
axiom $Is(#_module.InfPath.Stop(), Tclass._module.InfPath());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.InfPath.Stop(), Tclass._module.InfPath(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.InfPath.Stop(), Tclass._module.InfPath(), $h));

// Depth-one case-split function
function $IsA#_module.InfPath(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.InfPath(d) } 
  $IsA#_module.InfPath(d)
     ==> _module.InfPath.Right_q(d)
       || _module.InfPath.Down_q(d)
       || _module.InfPath.Stop_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.InfPath.Stop_q(d), $Is(d, Tclass._module.InfPath()) } 
    { _module.InfPath.Down_q(d), $Is(d, Tclass._module.InfPath()) } 
    { _module.InfPath.Right_q(d), $Is(d, Tclass._module.InfPath()) } 
  $Is(d, Tclass._module.InfPath())
     ==> _module.InfPath.Right_q(d)
       || _module.InfPath.Down_q(d)
       || _module.InfPath.Stop_q(d));

function $Eq#_module.InfPath(LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.InfPath($LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.InfPath()) && $Is(d1, Tclass._module.InfPath())
     ==> ($Eq#_module.InfPath($LS(ly), d0, d1)
       <==> (
          _module.InfPath.Right_q(d0)
           && _module.InfPath.Right_q(d1)
           && (_module.InfPath.Right_q(d0) && _module.InfPath.Right_q(d1)
             ==> $Eq#_module.InfPath(ly, _module.InfPath._h6(d0), _module.InfPath._h6(d1))))
         || (
          _module.InfPath.Down_q(d0)
           && _module.InfPath.Down_q(d1)
           && (_module.InfPath.Down_q(d0) && _module.InfPath.Down_q(d1)
             ==> $Eq#_module.InfPath(ly, _module.InfPath._h7(d0), _module.InfPath._h7(d1))))
         || (_module.InfPath.Stop_q(d0) && _module.InfPath.Stop_q(d1))));

// Unbump layer co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.InfPath($LS(ly), d0, d1) } 
  $Eq#_module.InfPath($LS(ly), d0, d1) <==> $Eq#_module.InfPath(ly, d0, d1));

// Equality for codatatypes
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.InfPath($LS(ly), d0, d1) } 
  $Eq#_module.InfPath($LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.InfPath(Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.InfPath(k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.InfPath()) && $Is(d1, Tclass._module.InfPath())
     ==> ($PrefixEq#_module.InfPath(k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (
              _module.InfPath.Right_q(d0)
               && _module.InfPath.Right_q(d1)
               && (_module.InfPath.Right_q(d0) && _module.InfPath.Right_q(d1)
                 ==> $PrefixEq#_module.InfPath(ORD#Minus(k, ORD#FromNat(1)), 
                  ly, 
                  _module.InfPath._h6(d0), 
                  _module.InfPath._h6(d1))))
             || (
              _module.InfPath.Down_q(d0)
               && _module.InfPath.Down_q(d1)
               && (_module.InfPath.Down_q(d0) && _module.InfPath.Down_q(d1)
                 ==> $PrefixEq#_module.InfPath(ORD#Minus(k, ORD#FromNat(1)), 
                  ly, 
                  _module.InfPath._h7(d0), 
                  _module.InfPath._h7(d1))))
             || (_module.InfPath.Stop_q(d0) && _module.InfPath.Stop_q(d1)))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k) ==> $Eq#_module.InfPath(ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.InfPath(k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.InfPath(k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.InfPath(k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.InfPath($LS(ly), d0, d1) } 
  $Eq#_module.InfPath($LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.InfPath(k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.InfPath(k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.InfPath($LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.InfPath(ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k ==> $PrefixEq#_module.InfPath(ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.InfPath($LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType, m: Box :: 
  { $PrefixEq#_module.InfPath(k, $LS(ly), d0, d1), $PrefixEq#_module.InfPath(m, $LS(ly), d0, d1) } 
  ORD#Less(k, m) && $PrefixEq#_module.InfPath(m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.InfPath(k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.InfPath(k, $LS(ly), d0, d1) } 
  d0 == d1 ==> $PrefixEq#_module.InfPath(k, $LS(ly), d0, d1));

const unique class._module.InfPath: ClassName;

// Constructor function declaration
function #_module.FinPath.Right(DatatypeType) : DatatypeType;

const unique ##_module.FinPath.Right: DtCtorId;

// Constructor identifier
axiom (forall a#68#0#0: DatatypeType :: 
  { #_module.FinPath.Right(a#68#0#0) } 
  DatatypeCtorId(#_module.FinPath.Right(a#68#0#0)) == ##_module.FinPath.Right);

function _module.FinPath.Right_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.FinPath.Right_q(d) } 
  _module.FinPath.Right_q(d) <==> DatatypeCtorId(d) == ##_module.FinPath.Right);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.FinPath.Right_q(d) } 
  _module.FinPath.Right_q(d)
     ==> (exists a#69#0#0: DatatypeType :: d == #_module.FinPath.Right(a#69#0#0)));

function Tclass._module.FinPath() : Ty;

const unique Tagclass._module.FinPath: TyTag;

// Tclass._module.FinPath Tag
axiom Tag(Tclass._module.FinPath()) == Tagclass._module.FinPath
   && TagFamily(Tclass._module.FinPath()) == tytagFamily$FinPath;

// Box/unbox axiom for Tclass._module.FinPath
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.FinPath()) } 
  $IsBox(bx, Tclass._module.FinPath())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.FinPath()));

// Constructor $Is
axiom (forall a#70#0#0: DatatypeType :: 
  { $Is(#_module.FinPath.Right(a#70#0#0), Tclass._module.FinPath()) } 
  $Is(#_module.FinPath.Right(a#70#0#0), Tclass._module.FinPath())
     <==> $Is(a#70#0#0, Tclass._module.FinPath()));

// Constructor $IsAlloc
axiom (forall a#71#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.FinPath.Right(a#71#0#0), Tclass._module.FinPath(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.FinPath.Right(a#71#0#0), Tclass._module.FinPath(), $h)
       <==> $IsAlloc(a#71#0#0, Tclass._module.FinPath(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.FinPath._h8(d), Tclass._module.FinPath(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.FinPath.Right_q(d)
       && $IsAlloc(d, Tclass._module.FinPath(), $h)
     ==> $IsAlloc(_module.FinPath._h8(d), Tclass._module.FinPath(), $h));

function _module.FinPath._h8(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#72#0#0: DatatypeType :: 
  { #_module.FinPath.Right(a#72#0#0) } 
  _module.FinPath._h8(#_module.FinPath.Right(a#72#0#0)) == a#72#0#0);

// Constructor function declaration
function #_module.FinPath.Down(DatatypeType) : DatatypeType;

const unique ##_module.FinPath.Down: DtCtorId;

// Constructor identifier
axiom (forall a#73#0#0: DatatypeType :: 
  { #_module.FinPath.Down(a#73#0#0) } 
  DatatypeCtorId(#_module.FinPath.Down(a#73#0#0)) == ##_module.FinPath.Down);

function _module.FinPath.Down_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.FinPath.Down_q(d) } 
  _module.FinPath.Down_q(d) <==> DatatypeCtorId(d) == ##_module.FinPath.Down);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.FinPath.Down_q(d) } 
  _module.FinPath.Down_q(d)
     ==> (exists a#74#0#0: DatatypeType :: d == #_module.FinPath.Down(a#74#0#0)));

// Constructor $Is
axiom (forall a#75#0#0: DatatypeType :: 
  { $Is(#_module.FinPath.Down(a#75#0#0), Tclass._module.FinPath()) } 
  $Is(#_module.FinPath.Down(a#75#0#0), Tclass._module.FinPath())
     <==> $Is(a#75#0#0, Tclass._module.FinPath()));

// Constructor $IsAlloc
axiom (forall a#76#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.FinPath.Down(a#76#0#0), Tclass._module.FinPath(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.FinPath.Down(a#76#0#0), Tclass._module.FinPath(), $h)
       <==> $IsAlloc(a#76#0#0, Tclass._module.FinPath(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.FinPath._h9(d), Tclass._module.FinPath(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.FinPath.Down_q(d)
       && $IsAlloc(d, Tclass._module.FinPath(), $h)
     ==> $IsAlloc(_module.FinPath._h9(d), Tclass._module.FinPath(), $h));

function _module.FinPath._h9(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#77#0#0: DatatypeType :: 
  { #_module.FinPath.Down(a#77#0#0) } 
  _module.FinPath._h9(#_module.FinPath.Down(a#77#0#0)) == a#77#0#0);

// Constructor function declaration
function #_module.FinPath.Stop() : DatatypeType;

const unique ##_module.FinPath.Stop: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.FinPath.Stop()) == ##_module.FinPath.Stop;

function _module.FinPath.Stop_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.FinPath.Stop_q(d) } 
  _module.FinPath.Stop_q(d) <==> DatatypeCtorId(d) == ##_module.FinPath.Stop);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.FinPath.Stop_q(d) } 
  _module.FinPath.Stop_q(d) ==> d == #_module.FinPath.Stop());

// Constructor $Is
axiom $Is(#_module.FinPath.Stop(), Tclass._module.FinPath());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.FinPath.Stop(), Tclass._module.FinPath(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.FinPath.Stop(), Tclass._module.FinPath(), $h));

// Depth-one case-split function
function $IsA#_module.FinPath(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.FinPath(d) } 
  $IsA#_module.FinPath(d)
     ==> _module.FinPath.Right_q(d)
       || _module.FinPath.Down_q(d)
       || _module.FinPath.Stop_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.FinPath.Stop_q(d), $Is(d, Tclass._module.FinPath()) } 
    { _module.FinPath.Down_q(d), $Is(d, Tclass._module.FinPath()) } 
    { _module.FinPath.Right_q(d), $Is(d, Tclass._module.FinPath()) } 
  $Is(d, Tclass._module.FinPath())
     ==> _module.FinPath.Right_q(d)
       || _module.FinPath.Down_q(d)
       || _module.FinPath.Stop_q(d));

function $Eq#_module.FinPath(LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.FinPath($LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.FinPath()) && $Is(d1, Tclass._module.FinPath())
     ==> ($Eq#_module.FinPath($LS(ly), d0, d1)
       <==> (
          _module.FinPath.Right_q(d0)
           && _module.FinPath.Right_q(d1)
           && (_module.FinPath.Right_q(d0) && _module.FinPath.Right_q(d1)
             ==> $Eq#_module.FinPath(ly, _module.FinPath._h8(d0), _module.FinPath._h8(d1))))
         || (
          _module.FinPath.Down_q(d0)
           && _module.FinPath.Down_q(d1)
           && (_module.FinPath.Down_q(d0) && _module.FinPath.Down_q(d1)
             ==> $Eq#_module.FinPath(ly, _module.FinPath._h9(d0), _module.FinPath._h9(d1))))
         || (_module.FinPath.Stop_q(d0) && _module.FinPath.Stop_q(d1))));

// Unbump layer co-equality axiom
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.FinPath($LS(ly), d0, d1) } 
  $Eq#_module.FinPath($LS(ly), d0, d1) <==> $Eq#_module.FinPath(ly, d0, d1));

// Equality for codatatypes
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.FinPath($LS(ly), d0, d1) } 
  $Eq#_module.FinPath($LS(ly), d0, d1) <==> d0 == d1);

function $PrefixEq#_module.FinPath(Box, LayerType, DatatypeType, DatatypeType) : bool;

// Layered co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.FinPath(k, $LS(ly), d0, d1) } 
  $Is(d0, Tclass._module.FinPath()) && $Is(d1, Tclass._module.FinPath())
     ==> ($PrefixEq#_module.FinPath(k, $LS(ly), d0, d1)
       <==> (0 < ORD#Offset(k)
           ==> (
              _module.FinPath.Right_q(d0)
               && _module.FinPath.Right_q(d1)
               && (_module.FinPath.Right_q(d0) && _module.FinPath.Right_q(d1)
                 ==> $PrefixEq#_module.FinPath(ORD#Minus(k, ORD#FromNat(1)), 
                  ly, 
                  _module.FinPath._h8(d0), 
                  _module.FinPath._h8(d1))))
             || (
              _module.FinPath.Down_q(d0)
               && _module.FinPath.Down_q(d1)
               && (_module.FinPath.Down_q(d0) && _module.FinPath.Down_q(d1)
                 ==> $PrefixEq#_module.FinPath(ORD#Minus(k, ORD#FromNat(1)), 
                  ly, 
                  _module.FinPath._h9(d0), 
                  _module.FinPath._h9(d1))))
             || (_module.FinPath.Stop_q(d0) && _module.FinPath.Stop_q(d1)))
         && (k != ORD#FromNat(0) && ORD#IsLimit(k) ==> $Eq#_module.FinPath(ly, d0, d1))));

// Unbump layer co-equality axiom
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.FinPath(k, $LS(ly), d0, d1) } 
  k != ORD#FromNat(0)
     ==> ($PrefixEq#_module.FinPath(k, $LS(ly), d0, d1)
       <==> $PrefixEq#_module.FinPath(k, ly, d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.FinPath($LS(ly), d0, d1) } 
  $Eq#_module.FinPath($LS(ly), d0, d1)
     <==> (forall k: Box :: 
      { $PrefixEq#_module.FinPath(k, $LS(ly), d0, d1) } 
      $PrefixEq#_module.FinPath(k, $LS(ly), d0, d1)));

// Coequality and prefix equality connection
axiom (forall ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $Eq#_module.FinPath($LS(ly), d0, d1) } 
  (forall k: int :: 
      { $PrefixEq#_module.FinPath(ORD#FromNat(k), $LS(ly), d0, d1) } 
      0 <= k ==> $PrefixEq#_module.FinPath(ORD#FromNat(k), $LS(ly), d0, d1))
     ==> $Eq#_module.FinPath($LS(ly), d0, d1));

// Prefix equality consequence
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType, m: Box :: 
  { $PrefixEq#_module.FinPath(k, $LS(ly), d0, d1), $PrefixEq#_module.FinPath(m, $LS(ly), d0, d1) } 
  ORD#Less(k, m) && $PrefixEq#_module.FinPath(m, $LS(ly), d0, d1)
     ==> $PrefixEq#_module.FinPath(k, $LS(ly), d0, d1));

// Prefix equality shortcut
axiom (forall k: Box, ly: LayerType, d0: DatatypeType, d1: DatatypeType :: 
  { $PrefixEq#_module.FinPath(k, $LS(ly), d0, d1) } 
  d0 == d1 ==> $PrefixEq#_module.FinPath(k, $LS(ly), d0, d1));

const unique class._module.FinPath: ClassName;

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

// function declaration for _module._default.Tail
function _module.__default.Tail(_module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int)
   : DatatypeType;

function _module.__default.Tail#canCall(_module._default.Tail$_T0: Ty, s#0: DatatypeType, n#0: int) : bool;

// layer synonym axiom
axiom (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
  { _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, n#0) } 
  _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, n#0)
     == _module.__default.Tail(_module._default.Tail$_T0, $ly, s#0, n#0));

// fuel synonym axiom
axiom (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
  { _module.__default.Tail(_module._default.Tail$_T0, AsFuelBottom($ly), s#0, n#0) } 
  _module.__default.Tail(_module._default.Tail$_T0, $ly, s#0, n#0)
     == _module.__default.Tail(_module._default.Tail$_T0, $LZ, s#0, n#0));

// consequence axiom for _module.__default.Tail
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    { _module.__default.Tail(_module._default.Tail$_T0, $ly, s#0, n#0) } 
    _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, n#0)
         || (19 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0))
           && LitInt(0) <= n#0)
       ==> $Is(_module.__default.Tail(_module._default.Tail$_T0, $ly, s#0, n#0), 
        Tclass._module.Stream(_module._default.Tail$_T0)));

function _module.__default.Tail#requires(Ty, LayerType, DatatypeType, int) : bool;

// #requires axiom for _module.__default.Tail
axiom (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
  { _module.__default.Tail#requires(_module._default.Tail$_T0, $ly, s#0, n#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0)) && LitInt(0) <= n#0
     ==> _module.__default.Tail#requires(_module._default.Tail$_T0, $ly, s#0, n#0)
       == true);

// definition axiom for _module.__default.Tail (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    { _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, n#0) } 
    _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, n#0)
         || (19 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0))
           && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0)
           ==> _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, n#0 - 1)
             && (var t#0 := _module.__default.Tail(_module._default.Tail$_T0, $ly, s#0, n#0 - 1); 
              $IsA#_module.Stream(t#0)))
         && _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, n#0)
           == (if n#0 == LitInt(0)
             then s#0
             else (var t#0 := _module.__default.Tail(_module._default.Tail$_T0, $ly, s#0, n#0 - 1); 
              (if $Eq#_module.Stream(_module._default.Tail$_T0, 
                  _module._default.Tail$_T0, 
                  $LS($LS($LZ)), 
                  t#0, 
                  #_module.Stream.Nil())
                 then t#0
                 else _module.Stream.tail(t#0)))));

// definition axiom for _module.__default.Tail for decreasing-related literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    {:weight 3} { _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, LitInt(n#0)) } 
    _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, LitInt(n#0))
         || (19 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0))
           && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, LitInt(n#0 - 1))
             && (var t#1 := _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, LitInt(n#0 - 1)); 
              $IsA#_module.Stream(t#1)))
         && _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then s#0
             else (var t#1 := _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), s#0, LitInt(n#0 - 1)); 
              (if $Eq#_module.Stream(_module._default.Tail$_T0, 
                  _module._default.Tail$_T0, 
                  $LS($LS($LZ)), 
                  t#1, 
                  #_module.Stream.Nil())
                 then t#1
                 else _module.Stream.tail(t#1)))));

// definition axiom for _module.__default.Tail for all literals (revealed)
axiom 19 <= $FunctionContextHeight
   ==> (forall _module._default.Tail$_T0: Ty, $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    {:weight 3} { _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), Lit(s#0), LitInt(n#0)) } 
    _module.__default.Tail#canCall(_module._default.Tail$_T0, Lit(s#0), LitInt(n#0))
         || (19 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0))
           && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.__default.Tail#canCall(_module._default.Tail$_T0, Lit(s#0), LitInt(n#0 - 1))
             && (var t#2 := Lit(_module.__default.Tail(_module._default.Tail$_T0, $LS($ly), Lit(s#0), LitInt(n#0 - 1))); 
              $IsA#_module.Stream(t#2)))
         && _module.__default.Tail(_module._default.Tail$_T0, $LS($ly), Lit(s#0), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then s#0
             else (var t#2 := Lit(_module.__default.Tail(_module._default.Tail$_T0, $LS($ly), Lit(s#0), LitInt(n#0 - 1))); 
              (if $Eq#_module.Stream(_module._default.Tail$_T0, 
                  _module._default.Tail$_T0, 
                  $LS($LS($LZ)), 
                  t#2, 
                  #_module.Stream.Nil())
                 then t#2
                 else _module.Stream.tail(t#2)))));

procedure CheckWellformed$$_module.__default.Tail(_module._default.Tail$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail$_T0)), 
    n#0: int where LitInt(0) <= n#0);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Tail(_module._default.Tail$_T0: Ty, s#0: DatatypeType, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Tail
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(9,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0), 
          Tclass._module.Stream(_module._default.Tail$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == LitInt(0))
        {
            assume _module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0) == s#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0), 
              Tclass._module.Stream(_module._default.Tail$_T0));
        }
        else
        {
            havoc t#Z#0;
            assume $Is(t#Z#0, Tclass._module.Stream(_module._default.Tail$_T0));
            ##s#0 := s#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Tail$_T0), $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, n#0 - 1);
            assume let#0#0#0
               == _module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0 - 1);
            assume _module.__default.Tail#canCall(_module._default.Tail$_T0, s#0, n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(_module._default.Tail$_T0));
            assume t#Z#0 == let#0#0#0;
            if ($Eq#_module.Stream(_module._default.Tail$_T0, 
              _module._default.Tail$_T0, 
              $LS($LS($LZ)), 
              t#Z#0, 
              #_module.Stream.Nil()))
            {
                assume _module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0) == t#Z#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0), 
                  Tclass._module.Stream(_module._default.Tail$_T0));
            }
            else
            {
                assert _module.Stream.Cons_q(t#Z#0);
                assume _module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0)
                   == _module.Stream.tail(t#Z#0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.Tail(_module._default.Tail$_T0, $LS($LZ), s#0, n#0), 
                  Tclass._module.Stream(_module._default.Tail$_T0));
            }
        }

        assert b$reqreads#0;
    }
}



procedure {:_induction s#0, n#0} CheckWellformed$$_module.__default.Tail__Lemma0(_module._default.Tail_Lemma0$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction s#0, n#0} CheckWellformed$$_module.__default.Tail__Lemma0(_module._default.Tail_Lemma0$_T0: Ty, s#0: DatatypeType, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var ##s#1: DatatypeType;
  var ##n#1: int;
  var ##s#2: DatatypeType;
  var ##n#2: int;

    // AddMethodImpl: Tail_Lemma0, CheckWellformed$$_module.__default.Tail__Lemma0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(16,6): initial state"} true;
    assume _module.Stream.Cons_q(s#0);
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0), $Heap);
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(_module._default.Tail_Lemma0$_T0, s#0, n#0);
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), s#0, n#0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(18,26): post-state"} true;
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0), $Heap);
    ##n#1 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(_module._default.Tail_Lemma0$_T0, s#0, n#0);
    assert _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), s#0, n#0));
    assert _module.Stream.Cons_q(s#0);
    ##s#2 := _module.Stream.tail(s#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0), $Heap);
    ##n#2 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(_module._default.Tail_Lemma0$_T0, _module.Stream.tail(s#0), n#0);
    assume $Eq#_module.Stream(_module._default.Tail_Lemma0$_T0, 
      _module._default.Tail_Lemma0$_T0, 
      $LS($LS($LZ)), 
      _module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), s#0, n#0)), 
      _module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), _module.Stream.tail(s#0), n#0));
}



procedure {:_induction s#0, n#0} Call$$_module.__default.Tail__Lemma0(_module._default.Tail_Lemma0$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0);
  // user-defined preconditions
  requires _module.Stream.Cons_q(s#0);
  requires _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LS($LZ)), s#0, n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), s#0, n#0)))
     && $IsA#_module.Stream(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), _module.Stream.tail(s#0), n#0))
     && 
    _module.__default.Tail#canCall(_module._default.Tail_Lemma0$_T0, s#0, n#0)
     && _module.__default.Tail#canCall(_module._default.Tail_Lemma0$_T0, _module.Stream.tail(s#0), n#0);
  ensures $Eq#_module.Stream(_module._default.Tail_Lemma0$_T0, 
    _module._default.Tail_Lemma0$_T0, 
    $LS($LS($LZ)), 
    _module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LS($LZ)), s#0, n#0)), 
    _module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LS($LZ)), _module.Stream.tail(s#0), n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, n#0} Impl$$_module.__default.Tail__Lemma0(_module._default.Tail_Lemma0$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0)
   returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.Stream.Cons_q(s#0);
  requires _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LS($LZ)), s#0, n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), s#0, n#0)))
     && $IsA#_module.Stream(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), _module.Stream.tail(s#0), n#0))
     && 
    _module.__default.Tail#canCall(_module._default.Tail_Lemma0$_T0, s#0, n#0)
     && _module.__default.Tail#canCall(_module._default.Tail_Lemma0$_T0, _module.Stream.tail(s#0), n#0);
  ensures $Eq#_module.Stream(_module._default.Tail_Lemma0$_T0, 
    _module._default.Tail_Lemma0$_T0, 
    $LS($LS($LZ)), 
    _module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LS($LZ)), s#0, n#0)), 
    _module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LS($LZ)), _module.Stream.tail(s#0), n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, n#0} Impl$$_module.__default.Tail__Lemma0(_module._default.Tail_Lemma0$_T0: Ty, s#0: DatatypeType, n#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Tail_Lemma0, Impl$$_module.__default.Tail__Lemma0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(19,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#n0#0: int :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Tail_Lemma0$_T0))
           && LitInt(0) <= $ih#n0#0
           && 
          _module.Stream.Cons_q($ih#s0#0)
           && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), $ih#s0#0, $ih#n0#0))
           && 
          0 <= $ih#n0#0
           && $ih#n0#0 < n#0
         ==> $Eq#_module.Stream(_module._default.Tail_Lemma0$_T0, 
          _module._default.Tail_Lemma0$_T0, 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma0$_T0, $LS($LZ), $ih#s0#0, $ih#n0#0)), 
          _module.__default.Tail(_module._default.Tail_Lemma0$_T0, 
            $LS($LZ), 
            _module.Stream.tail($ih#s0#0), 
            $ih#n0#0)));
    $_reverifyPost := false;
}



procedure {:_induction s#0, k#0, n#0} CheckWellformed$$_module.__default.Tail__Lemma1(_module._default.Tail_Lemma1$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    k#0: int where LitInt(0) <= k#0, 
    n#0: int where LitInt(0) <= n#0);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0, k#0, n#0} Call$$_module.__default.Tail__Lemma1(_module._default.Tail_Lemma1$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    k#0: int where LitInt(0) <= k#0, 
    n#0: int where LitInt(0) <= n#0);
  // user-defined preconditions
  requires k#0 <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, n#0)
     && (_module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0))
       ==> _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, k#0));
  ensures _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0))
     ==> _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LS($LZ)), s#0, k#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, k#0, n#0} Impl$$_module.__default.Tail__Lemma1(_module._default.Tail_Lemma1$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    k#0: int where LitInt(0) <= k#0, 
    n#0: int where LitInt(0) <= n#0)
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  // user-defined preconditions
  requires k#0 <= n#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, n#0)
     && (_module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0))
       ==> _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, k#0));
  ensures _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0))
     ==> _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LS($LZ)), s#0, k#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, k#0, n#0} Impl$$_module.__default.Tail__Lemma1(_module._default.Tail_Lemma1$_T0: Ty, s#0: DatatypeType, k#0: int, n#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##s#2: DatatypeType;
  var ##n#2: int;
  var ##s#0_0: DatatypeType;
  var ##n#0_0: int;
  var ##s#0_1: DatatypeType;
  var ##n#0_1: int;

    // AddMethodImpl: Tail_Lemma1, Impl$$_module.__default.Tail__Lemma1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(25,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#k0#0: int, $ih#n0#0: int :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0))
           && LitInt(0) <= $ih#k0#0
           && LitInt(0) <= $ih#n0#0
           && $ih#k0#0 <= $ih#n0#0
           && ((0 <= $ih#k0#0 && $ih#k0#0 < k#0)
             || ($ih#k0#0 == k#0 && 0 <= $ih#n0#0 && $ih#n0#0 < n#0))
         ==> 
        _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), $ih#s0#0, $ih#n0#0))
         ==> _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), $ih#s0#0, $ih#k0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(26,3)
    if (k#0 < n#0)
    {
        ##s#2 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#2, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0), $Heap);
        ##n#2 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, n#0);
    }

    assume k#0 < n#0
       ==> _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, n#0);
    if (k#0 < n#0
       && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0)))
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(27,5)
        ##s#0_0 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0), $Heap);
        ##n#0_0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, n#0);
        ##s#0_1 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_1, Tclass._module.Stream(_module._default.Tail_Lemma1$_T0), $Heap);
        assert $Is(n#0 - 1, Tclass._System.nat());
        ##n#0_1 := n#0 - 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_1, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, n#0 - 1);
        assert _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0 - 1));
        assume $IsA#_module.Stream(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0))
           && $IsA#_module.Stream(_module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0 - 1)))
           && 
          _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, n#0)
           && _module.__default.Tail#canCall(_module._default.Tail_Lemma1$_T0, s#0, n#0 - 1);
        assert {:subsumption 0} $Eq#_module.Stream(_module._default.Tail_Lemma1$_T0, 
          _module._default.Tail_Lemma1$_T0, 
          $LS($LS($LZ)), 
          _module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LS($LZ)), s#0, n#0), 
          _module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LS($LZ)), s#0, n#0 - 1)));
        assume $Eq#_module.Stream(_module._default.Tail_Lemma1$_T0, 
          _module._default.Tail_Lemma1$_T0, 
          $LS($LS($LZ)), 
          _module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0), 
          _module.Stream.tail(_module.__default.Tail(_module._default.Tail_Lemma1$_T0, $LS($LZ), s#0, n#0 - 1)));
    }
    else
    {
    }
}



procedure {:_induction s#0, n#0} CheckWellformed$$_module.__default.Tail__Lemma2(_module._default.Tail_Lemma2$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0);
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction s#0, n#0} CheckWellformed$$_module.__default.Tail__Lemma2(_module._default.Tail_Lemma2$_T0: Ty, s#0: DatatypeType, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var ##s#1: DatatypeType;
  var ##n#1: int;

    // AddMethodImpl: Tail_Lemma2, CheckWellformed$$_module.__default.Tail__Lemma2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(30,6): initial state"} true;
    assume _module.Stream.Cons_q(s#0);
    assert _module.Stream.Cons_q(s#0);
    ##s#0 := _module.Stream.tail(s#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0), $Heap);
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(_module._default.Tail_Lemma2$_T0, _module.Stream.tail(s#0), n#0);
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma2$_T0, $LS($LZ), _module.Stream.tail(s#0), n#0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(32,21): post-state"} true;
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0), $Heap);
    ##n#1 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(_module._default.Tail_Lemma2$_T0, s#0, n#0);
    assume _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma2$_T0, $LS($LZ), s#0, n#0));
}



procedure {:_induction s#0, n#0} Call$$_module.__default.Tail__Lemma2(_module._default.Tail_Lemma2$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0);
  // user-defined preconditions
  requires _module.Stream.Cons_q(s#0);
  requires _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma2$_T0, $LS($LS($LZ)), _module.Stream.tail(s#0), n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Tail#canCall(_module._default.Tail_Lemma2$_T0, s#0, n#0);
  ensures _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma2$_T0, $LS($LS($LZ)), s#0, n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, n#0} Impl$$_module.__default.Tail__Lemma2(_module._default.Tail_Lemma2$_T0: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0)
   returns ($_reverifyPost: bool);
  free requires 42 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.Stream.Cons_q(s#0);
  requires _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma2$_T0, $LS($LS($LZ)), _module.Stream.tail(s#0), n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Tail#canCall(_module._default.Tail_Lemma2$_T0, s#0, n#0);
  ensures _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma2$_T0, $LS($LS($LZ)), s#0, n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, n#0} Impl$$_module.__default.Tail__Lemma2(_module._default.Tail_Lemma2$_T0: Ty, s#0: DatatypeType, n#0: int)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var s##0_0: DatatypeType;
  var n##0_0: int;

    // AddMethodImpl: Tail_Lemma2, Impl$$_module.__default.Tail__Lemma2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(33,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#n0#0: int :: 
      $Is($ih#s0#0, Tclass._module.Stream(_module._default.Tail_Lemma2$_T0))
           && LitInt(0) <= $ih#n0#0
           && 
          _module.Stream.Cons_q($ih#s0#0)
           && _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma2$_T0, 
              $LS($LZ), 
              _module.Stream.tail($ih#s0#0), 
              $ih#n0#0))
           && 
          0 <= $ih#n0#0
           && $ih#n0#0 < n#0
         ==> _module.Stream.Cons_q(_module.__default.Tail(_module._default.Tail_Lemma2$_T0, $LS($LZ), $ih#s0#0, $ih#n0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(34,3)
    assume true;
    if (n#0 != 0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(35,16)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0_0 := s#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0 - 1, Tclass._System.nat());
        n##0_0 := n#0 - 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Tail__Lemma0(_module._default.Tail_Lemma2$_T0, s##0_0, n##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(35,23)"} true;
    }
    else
    {
    }
}



// function declaration for _module._default.IsNeverEndingStream
function _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S: Ty, $ly: LayerType, s#0: DatatypeType)
   : bool;

function _module.__default.IsNeverEndingStream#canCall(_module._default.IsNeverEndingStream$S: Ty, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.IsNeverEndingStream$S: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($ly), s#0) } 
  _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($ly), s#0)
     == _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $ly, s#0));

// fuel synonym axiom
axiom (forall _module._default.IsNeverEndingStream$S: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, AsFuelBottom($ly), s#0) } 
  _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $ly, s#0)
     == _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LZ, s#0));

// consequence axiom for _module.__default.IsNeverEndingStream
axiom 1 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream$S: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $ly, s#0) } 
    _module.__default.IsNeverEndingStream#canCall(_module._default.IsNeverEndingStream$S, s#0)
         || (1 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream$S)))
       ==> true);

function _module.__default.IsNeverEndingStream#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.IsNeverEndingStream
axiom (forall _module._default.IsNeverEndingStream$S: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.IsNeverEndingStream#requires(_module._default.IsNeverEndingStream$S, $ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream$S))
     ==> _module.__default.IsNeverEndingStream#requires(_module._default.IsNeverEndingStream$S, $ly, s#0)
       == true);

// definition axiom for _module.__default.IsNeverEndingStream (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream$S: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($ly), s#0) } 
    _module.__default.IsNeverEndingStream#canCall(_module._default.IsNeverEndingStream$S, s#0)
         || (1 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream$S)))
       ==> (!_module.Stream.Nil_q(s#0)
           ==> (var tail#1 := _module.Stream.tail(s#0); 
            _module.__default.IsNeverEndingStream#canCall(_module._default.IsNeverEndingStream$S, tail#1)))
         && _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($ly), s#0)
           == (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#0 := _module.Stream.tail(s#0); 
              _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $ly, tail#0))));

// 1st prefix predicate axiom for _module.__default.IsNeverEndingStream_h
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream#$S: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream#$S, $LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream#$S))
         && _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream#$S, $LS($ly), s#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k#0, s#0) } 
        _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k#0, s#0)));

// 2nd prefix predicate axiom
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream#$S: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream#$S, $LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream#$S))
         && (forall _k#0: Box :: 
          { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k#0, s#0) } 
          _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k#0, s#0))
       ==> _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream#$S, $LS($ly), s#0));

// 3rd prefix predicate axiom
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream#$S: Ty, 
      $ly: LayerType, 
      s#0: DatatypeType, 
      _k#0: Box :: 
    { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $ly, _k#0, s#0) } 
    $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream#$S))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $ly, _k#0, s#0));

procedure CheckWellformed$$_module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S: Ty, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream$S)));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S: Ty, s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function IsNeverEndingStream
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(41,19): initial state"} true;
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
        if (s#0 == #_module.Stream.Nil())
        {
            assume _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($LZ), s#0)
               == Lit(false);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($LZ), s#0), 
              TBool);
        }
        else if (s#0 == #_module.Stream.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.IsNeverEndingStream$S);
            assume $Is(_mcc#1#0, Tclass._module.Stream(_module._default.IsNeverEndingStream$S));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.Stream(_module._default.IsNeverEndingStream$S));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(_module._default.IsNeverEndingStream$S));
            assume tail#Z#0 == let#0#0#0;
            ##s#0 := tail#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream$S), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.IsNeverEndingStream#canCall(_module._default.IsNeverEndingStream$S, tail#Z#0);
            assume _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($LZ), s#0)
               == _module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($LZ), tail#Z#0);
            assume _module.__default.IsNeverEndingStream#canCall(_module._default.IsNeverEndingStream$S, tail#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.IsNeverEndingStream(_module._default.IsNeverEndingStream$S, $LS($LZ), s#0), 
              TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.IsNeverEndingStream#
function _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType)
   : bool;

function _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S: Ty, _k#0: Box, s#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.IsNeverEndingStream#$S: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType :: 
  { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k#0, s#0) } 
  _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k#0, s#0)
     == _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $ly, _k#0, s#0));

// fuel synonym axiom
axiom (forall _module._default.IsNeverEndingStream#$S: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType :: 
  { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, AsFuelBottom($ly), _k#0, s#0) } 
  _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $ly, _k#0, s#0)
     == _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LZ, _k#0, s#0));

// consequence axiom for _module.__default.IsNeverEndingStream_h
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream#$S: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType :: 
    { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $ly, _k#0, s#0) } 
    _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, _k#0, s#0)
         || (2 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream#$S)))
       ==> true);

function _module.__default.IsNeverEndingStream_h#requires(Ty, LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.IsNeverEndingStream_h
axiom (forall _module._default.IsNeverEndingStream#$S: Ty, 
    $ly: LayerType, 
    _k#0: Box, 
    s#0: DatatypeType :: 
  { _module.__default.IsNeverEndingStream_h#requires(_module._default.IsNeverEndingStream#$S, $ly, _k#0, s#0) } 
  $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream#$S))
     ==> _module.__default.IsNeverEndingStream_h#requires(_module._default.IsNeverEndingStream#$S, $ly, _k#0, s#0)
       == true);

// definition axiom for _module.__default.IsNeverEndingStream_h (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream#$S: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType :: 
    { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k#0, s#0) } 
    _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, _k#0, s#0)
         || (2 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream#$S)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#3 := _module.Stream.tail(s#0); 
            _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, ORD#Minus(_k#0, ORD#FromNat(1)), tail#3)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#4 := _module.Stream.tail(s#0); 
              _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, 
                $ly, 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                tail#4))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $ly, _k'#0, s#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, _k'#0, s#0)))
         && _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k#0, s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#2 := _module.Stream.tail(s#0); 
                  _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, 
                    $ly, 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    tail#2))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $ly, _k'#0, s#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $ly, _k'#0, s#0)))));

// definition axiom for _module.__default.IsNeverEndingStream_h for decreasing-related literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream#$S: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType :: 
    {:weight 3} { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), Lit(_k#0), s#0) } 
    _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, Lit(_k#0), s#0)
         || (2 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream#$S)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#6 := _module.Stream.tail(s#0); 
            _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, ORD#Minus(_k#0, ORD#FromNat(1)), tail#6)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#7 := _module.Stream.tail(s#0); 
              _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, 
                $LS($ly), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                tail#7))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k'#1, s#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, _k'#1, s#0)))
         && _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), Lit(_k#0), s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#5 := _module.Stream.tail(s#0); 
                  _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, 
                    $LS($ly), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    tail#5))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k'#1, s#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k'#1, s#0)))));

// definition axiom for _module.__default.IsNeverEndingStream_h for all literals (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall _module._default.IsNeverEndingStream#$S: Ty, 
      $ly: LayerType, 
      _k#0: Box, 
      s#0: DatatypeType :: 
    {:weight 3} { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), Lit(_k#0), Lit(s#0)) } 
    _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, Lit(_k#0), Lit(s#0))
         || (2 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(_module._default.IsNeverEndingStream#$S)))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#9 := _module.Stream.tail(s#0); 
            _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, ORD#Minus(_k#0, ORD#FromNat(1)), tail#9)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#10 := _module.Stream.tail(s#0); 
              _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, 
                $LS($ly), 
                ORD#Minus(_k#0, ORD#FromNat(1)), 
                tail#10))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k'#2, s#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.IsNeverEndingStream_h#canCall(_module._default.IsNeverEndingStream#$S, _k'#2, s#0)))
         && _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), Lit(_k#0), Lit(s#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#8 := _module.Stream.tail(s#0); 
                  _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, 
                    $LS($ly), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    tail#8))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k'#2, s#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.IsNeverEndingStream_h(_module._default.IsNeverEndingStream#$S, $LS($ly), _k'#2, s#0)))));

// function declaration for _module._default.AnInfiniteStream
function _module.__default.AnInfiniteStream($ly: LayerType) : DatatypeType;

function _module.__default.AnInfiniteStream#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.AnInfiniteStream($LS($ly)) } 
  _module.__default.AnInfiniteStream($LS($ly))
     == _module.__default.AnInfiniteStream($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.AnInfiniteStream(AsFuelBottom($ly)) } 
  _module.__default.AnInfiniteStream($ly)
     == _module.__default.AnInfiniteStream($LZ));

// consequence axiom for _module.__default.AnInfiniteStream
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.AnInfiniteStream($ly) } 
    _module.__default.AnInfiniteStream#canCall() || 3 != $FunctionContextHeight
       ==> $Is(_module.__default.AnInfiniteStream($ly), Tclass._module.Stream(TInt)));

function _module.__default.AnInfiniteStream#requires(LayerType) : bool;

// #requires axiom for _module.__default.AnInfiniteStream
axiom (forall $ly: LayerType :: 
  { _module.__default.AnInfiniteStream#requires($ly) } 
  _module.__default.AnInfiniteStream#requires($ly) == true);

// definition axiom for _module.__default.AnInfiniteStream (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.AnInfiniteStream($LS($ly)) } 
    _module.__default.AnInfiniteStream#canCall() || 3 != $FunctionContextHeight
       ==> _module.__default.AnInfiniteStream#canCall()
         && _module.__default.AnInfiniteStream($LS($ly))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.AnInfiniteStream($ly)))));

procedure CheckWellformed$$_module.__default.AnInfiniteStream();
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.AnInfiniteStream()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function AnInfiniteStream
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(50,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.AnInfiniteStream($LS($LZ)), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.AnInfiniteStream#canCall();
        assume _module.__default.AnInfiniteStream($LS($LZ))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.AnInfiniteStream($LS($LZ)))));
        assume _module.__default.AnInfiniteStream#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.AnInfiniteStream($LS($LZ)), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.Proposition0();
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Proposition0();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AnInfiniteStream#canCall()
     && _module.__default.IsNeverEndingStream#canCall(TInt, Lit(_module.__default.AnInfiniteStream($LS($LZ))));
  ensures Lit(_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), Lit(_module.__default.AnInfiniteStream($LS($LS($LZ))))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} CoCall$$_module.__default.Proposition0_h(_k#0: Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AnInfiniteStream#canCall()
     && _module.__default.IsNeverEndingStream_h#canCall(TInt, _k#0, Lit(_module.__default.AnInfiniteStream($LS($LZ))));
  ensures _module.__default.IsNeverEndingStream_h(TInt, 
    $LS($LS($LZ)), 
    _k#0, 
    Lit(_module.__default.AnInfiniteStream($LS($LS($LZ)))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} Impl$$_module.__default.Proposition0_h(_k#0: Box) returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.AnInfiniteStream#canCall()
     && _module.__default.IsNeverEndingStream_h#canCall(TInt, _k#0, Lit(_module.__default.AnInfiniteStream($LS($LZ))));
  ensures _module.__default.IsNeverEndingStream_h(TInt, 
    $LS($LS($LZ)), 
    _k#0, 
    Lit(_module.__default.AnInfiniteStream($LS($LS($LZ)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0} Impl$$_module.__default.Proposition0_h(_k#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Proposition0#, Impl$$_module.__default.Proposition0_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(54,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box :: 
      Lit(true) && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.IsNeverEndingStream_h(TInt, $LS($LZ), $ih#_k0#0, Lit(_module.__default.AnInfiniteStream($LS($LZ)))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(56,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(54,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box :: 
          ORD#Less(_k'#0, _k#0)
             ==> _module.__default.IsNeverEndingStream_h(TInt, $LS($LZ), _k'#0, Lit(_module.__default.AnInfiniteStream($LS($LZ)))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(54,15)"} true;
    }
}



// function declaration for _module._default.HasBoundedHeight
function _module.__default.HasBoundedHeight(t#0: DatatypeType) : bool;

function _module.__default.HasBoundedHeight#canCall(t#0: DatatypeType) : bool;

// consequence axiom for _module.__default.HasBoundedHeight
axiom 43 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.HasBoundedHeight(t#0) } 
    _module.__default.HasBoundedHeight#canCall(t#0)
         || (43 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> true);

function _module.__default.HasBoundedHeight#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.HasBoundedHeight
axiom (forall t#0: DatatypeType :: 
  { _module.__default.HasBoundedHeight#requires(t#0) } 
  $Is(t#0, Tclass._module.Tree())
     ==> _module.__default.HasBoundedHeight#requires(t#0) == true);

// definition axiom for _module.__default.HasBoundedHeight (revealed)
axiom 43 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.HasBoundedHeight(t#0) } 
    _module.__default.HasBoundedHeight#canCall(t#0)
         || (43 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (forall n#0: int :: 
          { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0) } 
          LitInt(0) <= n#0
             ==> 
            LitInt(0) <= n#0
             ==> _module.Tree.Node_q(t#0)
               && _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#0))
         && _module.__default.HasBoundedHeight(t#0)
           == (exists n#0: int :: 
            { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0) } 
            LitInt(0) <= n#0
               && 
              LitInt(0) <= n#0
               && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0)));

// definition axiom for _module.__default.HasBoundedHeight for all literals (revealed)
axiom 43 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    {:weight 3} { _module.__default.HasBoundedHeight(Lit(t#0)) } 
    _module.__default.HasBoundedHeight#canCall(Lit(t#0))
         || (43 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (forall n#1: int :: 
          { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#1) } 
          LitInt(0) <= n#1
             ==> 
            LitInt(0) <= n#1
             ==> _module.Tree.Node_q(Lit(t#0))
               && _module.__default.LowerThan#canCall(Lit(_module.Tree.children(Lit(t#0))), n#1))
         && _module.__default.HasBoundedHeight(Lit(t#0))
           == (exists n#1: int :: 
            { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#1) } 
            LitInt(0) <= n#1
               && 
              LitInt(0) <= n#1
               && _module.__default.LowerThan($LS($LZ), Lit(_module.Tree.children(Lit(t#0))), n#1)));

procedure CheckWellformed$$_module.__default.HasBoundedHeight(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()));
  free requires 43 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.HasBoundedHeight(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#2: int;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function HasBoundedHeight
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(67,10): initial state"} true;
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
        // Begin Comprehension WF check
        havoc n#2;
        if (LitInt(0) <= n#2)
        {
            if (LitInt(0) <= n#2)
            {
                assume _module.Tree.Node_q(t#0);
                ##s#0 := _module.Tree.children(t#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#0 := n#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#2);
            }
        }

        // End Comprehension WF check
        assume _module.__default.HasBoundedHeight(t#0)
           == (exists n#3: int :: 
            { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#3) } 
            LitInt(0) <= n#3
               && 
              LitInt(0) <= n#3
               && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#3));
        assume (forall n#3: int :: 
          { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#3) } 
          LitInt(0) <= n#3
             ==> 
            LitInt(0) <= n#3
             ==> _module.Tree.Node_q(t#0)
               && _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#3));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.HasBoundedHeight(t#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.LowerThan
function _module.__default.LowerThan($ly: LayerType, s#0: DatatypeType, n#0: int) : bool;

function _module.__default.LowerThan#canCall(s#0: DatatypeType, n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType, n#0: int :: 
  { _module.__default.LowerThan($LS($ly), s#0, n#0) } 
  _module.__default.LowerThan($LS($ly), s#0, n#0)
     == _module.__default.LowerThan($ly, s#0, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType, n#0: int :: 
  { _module.__default.LowerThan(AsFuelBottom($ly), s#0, n#0) } 
  _module.__default.LowerThan($ly, s#0, n#0)
     == _module.__default.LowerThan($LZ, s#0, n#0));

// consequence axiom for _module.__default.LowerThan
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    { _module.__default.LowerThan($ly, s#0, n#0) } 
    _module.__default.LowerThan#canCall(s#0, n#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= n#0)
       ==> true);

function _module.__default.LowerThan#requires(LayerType, DatatypeType, int) : bool;

// #requires axiom for _module.__default.LowerThan
axiom (forall $ly: LayerType, s#0: DatatypeType, n#0: int :: 
  { _module.__default.LowerThan#requires($ly, s#0, n#0) } 
  $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())) && LitInt(0) <= n#0
     ==> _module.__default.LowerThan#requires($ly, s#0, n#0) == true);

// definition axiom for _module.__default.LowerThan (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    { _module.__default.LowerThan($LS($ly), s#0, n#0) } 
    _module.__default.LowerThan#canCall(s#0, n#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= n#0)
       ==> (!_module.Stream.Nil_q(s#0)
           ==> (var tail#1 := _module.Stream.tail(s#0); 
            (var t#1 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              LitInt(1) <= n#0
                 ==> _module.Tree.Node_q(t#1)
                   && _module.__default.LowerThan#canCall(_module.Tree.children(t#1), n#0 - 1)
                   && (_module.__default.LowerThan($ly, _module.Tree.children(t#1), n#0 - 1)
                     ==> _module.__default.LowerThan#canCall(tail#1, n#0)))))
         && _module.__default.LowerThan($LS($ly), s#0, n#0)
           == (if _module.Stream.Nil_q(s#0)
             then true
             else (var tail#0 := _module.Stream.tail(s#0); 
              (var t#0 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                LitInt(1) <= n#0
                   && _module.__default.LowerThan($ly, _module.Tree.children(t#0), n#0 - 1)
                   && _module.__default.LowerThan($ly, tail#0, n#0)))));

// 1st prefix predicate axiom for _module.__default.LowerThan_h
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    { _module.__default.LowerThan($LS($ly), s#0, n#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && LitInt(0) <= n#0
         && _module.__default.LowerThan($LS($ly), s#0, n#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.LowerThan_h($LS($ly), _k#0, s#0, n#0) } 
        _module.__default.LowerThan_h($LS($ly), _k#0, s#0, n#0)));

// 2nd prefix predicate axiom
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, n#0: int :: 
    { _module.__default.LowerThan($LS($ly), s#0, n#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && LitInt(0) <= n#0
         && (forall _k#0: Box :: 
          { _module.__default.LowerThan_h($LS($ly), _k#0, s#0, n#0) } 
          _module.__default.LowerThan_h($LS($ly), _k#0, s#0, n#0))
       ==> _module.__default.LowerThan($LS($ly), s#0, n#0));

// 3rd prefix predicate axiom
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, n#0: int, _k#0: Box :: 
    { _module.__default.LowerThan_h($ly, _k#0, s#0, n#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && LitInt(0) <= n#0
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.LowerThan_h($ly, _k#0, s#0, n#0));

procedure CheckWellformed$$_module.__default.LowerThan(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())), 
    n#0: int where LitInt(0) <= n#0);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.LowerThan(s#0: DatatypeType, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var t#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var ##s#1: DatatypeType;
  var ##n#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function LowerThan
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(71,19): initial state"} true;
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
        if (s#0 == #_module.Stream.Nil())
        {
            assume _module.__default.LowerThan($LS($LZ), s#0, n#0) == Lit(true);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.LowerThan($LS($LZ), s#0, n#0), TBool);
        }
        else if (s#0 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Tree());
            assume $Is(_mcc#1#0, Tclass._module.Stream(Tclass._module.Tree()));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.Stream(Tclass._module.Tree()));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(Tclass._module.Tree()));
            assume tail#Z#0 == let#0#0#0;
            havoc t#Z#0;
            assume $Is(t#Z#0, Tclass._module.Tree());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Tree());
            assume t#Z#0 == let#1#0#0;
            if (LitInt(1) <= n#0)
            {
                assume _module.Tree.Node_q(t#Z#0);
                ##s#0 := _module.Tree.children(t#Z#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                assert $Is(n#0 - 1, Tclass._System.nat());
                ##n#0 := n#0 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.LowerThan#canCall(_module.Tree.children(t#Z#0), n#0 - 1);
            }

            if (LitInt(1) <= n#0
               && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#Z#0), n#0 - 1))
            {
                ##s#1 := tail#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#1 := n#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.LowerThan#canCall(tail#Z#0, n#0);
            }

            assume _module.__default.LowerThan($LS($LZ), s#0, n#0)
               == (
                LitInt(1) <= n#0
                 && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#Z#0), n#0 - 1)
                 && _module.__default.LowerThan($LS($LZ), tail#Z#0, n#0));
            assume LitInt(1) <= n#0
               ==> _module.Tree.Node_q(t#Z#0)
                 && _module.__default.LowerThan#canCall(_module.Tree.children(t#Z#0), n#0 - 1)
                 && (_module.__default.LowerThan($LS($LZ), _module.Tree.children(t#Z#0), n#0 - 1)
                   ==> _module.__default.LowerThan#canCall(tail#Z#0, n#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.LowerThan($LS($LZ), s#0, n#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.LowerThan#
function _module.__default.LowerThan_h($ly: LayerType, _k#0: Box, s#0: DatatypeType, n#0: int) : bool;

function _module.__default.LowerThan_h#canCall(_k#0: Box, s#0: DatatypeType, n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, n#0: int :: 
  { _module.__default.LowerThan_h($LS($ly), _k#0, s#0, n#0) } 
  _module.__default.LowerThan_h($LS($ly), _k#0, s#0, n#0)
     == _module.__default.LowerThan_h($ly, _k#0, s#0, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, n#0: int :: 
  { _module.__default.LowerThan_h(AsFuelBottom($ly), _k#0, s#0, n#0) } 
  _module.__default.LowerThan_h($ly, _k#0, s#0, n#0)
     == _module.__default.LowerThan_h($LZ, _k#0, s#0, n#0));

// consequence axiom for _module.__default.LowerThan_h
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, n#0: int :: 
    { _module.__default.LowerThan_h($ly, _k#0, s#0, n#0) } 
    _module.__default.LowerThan_h#canCall(_k#0, s#0, n#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= n#0)
       ==> true);

function _module.__default.LowerThan_h#requires(LayerType, Box, DatatypeType, int) : bool;

// #requires axiom for _module.__default.LowerThan_h
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, n#0: int :: 
  { _module.__default.LowerThan_h#requires($ly, _k#0, s#0, n#0) } 
  $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())) && LitInt(0) <= n#0
     ==> _module.__default.LowerThan_h#requires($ly, _k#0, s#0, n#0) == true);

// definition axiom for _module.__default.LowerThan_h (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, n#0: int :: 
    { _module.__default.LowerThan_h($LS($ly), _k#0, s#0, n#0) } 
    _module.__default.LowerThan_h#canCall(_k#0, s#0, n#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= n#0)
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#3 := _module.Stream.tail(s#0); 
            (var t#3 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              LitInt(1) <= n#0
                 ==> _module.Tree.Node_q(t#3)
                   && _module.__default.LowerThan_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#3), n#0 - 1)
                   && (_module.__default.LowerThan_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#3), n#0 - 1)
                     ==> _module.__default.LowerThan_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#3, n#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then true
             else (var tail#4 := _module.Stream.tail(s#0); 
              (var t#4 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                LitInt(1) <= n#0
                   && _module.__default.LowerThan_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#4), n#0 - 1)
                   && _module.__default.LowerThan_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), tail#4, n#0)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.LowerThan_h($ly, _k'#0, s#0, n#0) } 
            ORD#Less(_k'#0, _k#0) ==> _module.__default.LowerThan_h#canCall(_k'#0, s#0, n#0)))
         && _module.__default.LowerThan_h($LS($ly), _k#0, s#0, n#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then true
                 else (var tail#2 := _module.Stream.tail(s#0); 
                  (var t#2 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    LitInt(1) <= n#0
                       && _module.__default.LowerThan_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#2), n#0 - 1)
                       && _module.__default.LowerThan_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), tail#2, n#0)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.LowerThan_h($ly, _k'#0, s#0, n#0) } 
                ORD#Less(_k'#0, _k#0) ==> _module.__default.LowerThan_h($ly, _k'#0, s#0, n#0)))));

// definition axiom for _module.__default.LowerThan_h for decreasing-related literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, n#0: int :: 
    {:weight 3} { _module.__default.LowerThan_h($LS($ly), Lit(_k#0), s#0, n#0) } 
    _module.__default.LowerThan_h#canCall(Lit(_k#0), s#0, n#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= n#0)
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#6 := _module.Stream.tail(s#0); 
            (var t#6 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              LitInt(1) <= n#0
                 ==> _module.Tree.Node_q(t#6)
                   && _module.__default.LowerThan_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#6), n#0 - 1)
                   && (_module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#6), n#0 - 1)
                     ==> _module.__default.LowerThan_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#6, n#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then true
             else (var tail#7 := _module.Stream.tail(s#0); 
              (var t#7 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                LitInt(1) <= n#0
                   && _module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#7), n#0 - 1)
                   && _module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#7, n#0)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.LowerThan_h($LS($ly), _k'#1, s#0, n#0) } 
            ORD#Less(_k'#1, _k#0) ==> _module.__default.LowerThan_h#canCall(_k'#1, s#0, n#0)))
         && _module.__default.LowerThan_h($LS($ly), Lit(_k#0), s#0, n#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then true
                 else (var tail#5 := _module.Stream.tail(s#0); 
                  (var t#5 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    LitInt(1) <= n#0
                       && _module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#5), n#0 - 1)
                       && _module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#5, n#0)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.LowerThan_h($LS($ly), _k'#1, s#0, n#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.LowerThan_h($LS($ly), _k'#1, s#0, n#0)))));

// definition axiom for _module.__default.LowerThan_h for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, n#0: int :: 
    {:weight 3} { _module.__default.LowerThan_h($LS($ly), Lit(_k#0), Lit(s#0), LitInt(n#0)) } 
    _module.__default.LowerThan_h#canCall(Lit(_k#0), Lit(s#0), LitInt(n#0))
         || (9 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= n#0)
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#9 := _module.Stream.tail(s#0); 
            (var t#9 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              LitInt(1) <= n#0
                 ==> _module.Tree.Node_q(t#9)
                   && _module.__default.LowerThan_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#9), n#0 - 1)
                   && (_module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#9), n#0 - 1)
                     ==> _module.__default.LowerThan_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#9, n#0)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then true
             else (var tail#10 := _module.Stream.tail(s#0); 
              (var t#10 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                LitInt(1) <= n#0
                   && _module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#10), n#0 - 1)
                   && _module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#10, n#0)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.LowerThan_h($LS($ly), _k'#2, s#0, n#0) } 
            ORD#Less(_k'#2, _k#0) ==> _module.__default.LowerThan_h#canCall(_k'#2, s#0, n#0)))
         && _module.__default.LowerThan_h($LS($ly), Lit(_k#0), Lit(s#0), LitInt(n#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then true
                 else (var tail#8 := _module.Stream.tail(s#0); 
                  (var t#8 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    LitInt(1) <= n#0
                       && _module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#8), n#0 - 1)
                       && _module.__default.LowerThan_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#8, n#0)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.LowerThan_h($LS($ly), _k'#2, s#0, n#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.LowerThan_h($LS($ly), _k'#2, s#0, n#0)))));

procedure {:_induction s#0, n#0, h#0} CheckWellformed$$_module.__default.LowerThan__Lemma(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0, 
    h#0: int where LitInt(0) <= h#0);
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction s#0, n#0, h#0} Call$$_module.__default.LowerThan__Lemma(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0, 
    h#0: int where LitInt(0) <= h#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LowerThan#canCall(s#0, h#0)
     && (_module.__default.LowerThan($LS($LZ), s#0, h#0)
       ==> _module.__default.Tail#canCall(Tclass._module.Tree(), s#0, n#0)
         && _module.__default.LowerThan#canCall(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#0, n#0), h#0));
  ensures _module.__default.LowerThan($LS($LZ), s#0, h#0)
     ==> _module.__default.LowerThan($LS($LS($LZ)), 
      _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#0, n#0), 
      h#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction s#0, n#0, h#0} Impl$$_module.__default.LowerThan__Lemma(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0, 
    h#0: int where LitInt(0) <= h#0)
   returns ($_reverifyPost: bool);
  free requires 44 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.LowerThan#canCall(s#0, h#0)
     && (_module.__default.LowerThan($LS($LZ), s#0, h#0)
       ==> _module.__default.Tail#canCall(Tclass._module.Tree(), s#0, n#0)
         && _module.__default.LowerThan#canCall(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#0, n#0), h#0));
  ensures _module.__default.LowerThan($LS($LZ), s#0, h#0)
     ==> _module.__default.LowerThan($LS($LS($LZ)), 
      _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#0, n#0), 
      h#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction s#0, n#0, h#0} Impl$$_module.__default.LowerThan__Lemma(s#0: DatatypeType, n#0: int, h#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var s##0: DatatypeType;
  var k##0: int;
  var n##0: int;
  var ##s#3: DatatypeType;
  var ##n#3: int;
  var _mcc#0#1_0: DatatypeType;
  var _mcc#1#1_0: DatatypeType;
  var tail#1_0: DatatypeType;
  var let#1_0#0#0: DatatypeType;
  var t#1_0: DatatypeType;
  var let#1_1#0#0: DatatypeType;
  var s##1_0: DatatypeType;
  var n##1_0: int;
  var h##1_0: int;
  var s##1_1: DatatypeType;
  var n##1_1: int;

    // AddMethodImpl: LowerThan_Lemma, Impl$$_module.__default.LowerThan__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(84,0): initial state"} true;
    assume $IsA#_module.Stream(s#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#s0#0: DatatypeType, $ih#n0#0: int, $ih#h0#0: int :: 
      $Is($ih#s0#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= $ih#n0#0
           && LitInt(0) <= $ih#h0#0
           && Lit(true)
           && ((0 <= $ih#n0#0 && $ih#n0#0 < n#0)
             || ($ih#n0#0 == n#0 && 0 <= $ih#h0#0 && $ih#h0#0 < h#0))
         ==> 
        _module.__default.LowerThan($LS($LZ), $ih#s0#0, $ih#h0#0)
         ==> _module.__default.LowerThan($LS($LZ), 
          _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), $ih#s0#0, $ih#n0#0), 
          $ih#h0#0));
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(85,14)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(LitInt(0), Tclass._System.nat());
    k##0 := LitInt(0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##0 := n#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Tail__Lemma1(Tclass._module.Tree(), s##0, k##0, n##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(85,22)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(86,3)
    if (n#0 != LitInt(0))
    {
        ##s#3 := s#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#3, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        ##n#3 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#0, n#0);
    }

    assume n#0 != LitInt(0)
       ==> $IsA#_module.Stream(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#0, n#0))
         && _module.__default.Tail#canCall(Tclass._module.Tree(), s#0, n#0);
    if (n#0 == LitInt(0)
       || $Eq#_module.Stream(Tclass._module.Tree(), 
        Tclass._module.Tree(), 
        $LS($LS($LZ)), 
        _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#0, n#0), 
        #_module.Stream.Nil()))
    {
    }
    else
    {
        assume true;
        havoc _mcc#0#1_0, _mcc#1#1_0;
        if (s#0 == #_module.Stream.Cons($Box(_mcc#0#1_0), _mcc#1#1_0))
        {
            assume $Is(_mcc#0#1_0, Tclass._module.Tree());
            assume $Is(_mcc#1#1_0, Tclass._module.Stream(Tclass._module.Tree()));
            havoc tail#1_0;
            assume $Is(tail#1_0, Tclass._module.Stream(Tclass._module.Tree()))
               && $IsAlloc(tail#1_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume let#1_0#0#0 == _mcc#1#1_0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1_0#0#0, Tclass._module.Stream(Tclass._module.Tree()));
            assume tail#1_0 == let#1_0#0#0;
            havoc t#1_0;
            assume $Is(t#1_0, Tclass._module.Tree())
               && $IsAlloc(t#1_0, Tclass._module.Tree(), $Heap);
            assume let#1_1#0#0 == _mcc#0#1_0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1_1#0#0, Tclass._module.Tree());
            assume t#1_0 == let#1_1#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(90,24)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##1_0 := tail#1_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0 - 1, Tclass._System.nat());
            n##1_0 := n#0 - 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            h##1_0 := h#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || n##1_0 == n#0;
            assert 0 <= h#0 || n##1_0 < n#0 || h##1_0 == h#0;
            assert n##1_0 < n#0 || (n##1_0 == n#0 && h##1_0 < h#0);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.LowerThan__Lemma(s##1_0, n##1_0, h##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(90,37)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(91,20)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##1_1 := s#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0 - 1, Tclass._System.nat());
            n##1_1 := n#0 - 1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Tail__Lemma0(Tclass._module.Tree(), s##1_1, n##1_1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(91,27)"} true;
        }
        else if (s#0 == #_module.Stream.Nil())
        {
            assert false;
        }
        else
        {
            assume false;
        }
    }
}



// function declaration for _module._default.IsFiniteSomewhere
function _module.__default.IsFiniteSomewhere(t#0: DatatypeType) : bool;

function _module.__default.IsFiniteSomewhere#canCall(t#0: DatatypeType) : bool;

// consequence axiom for _module.__default.IsFiniteSomewhere
axiom 45 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.IsFiniteSomewhere(t#0) } 
    _module.__default.IsFiniteSomewhere#canCall(t#0)
         || (45 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> true);

function _module.__default.IsFiniteSomewhere#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.IsFiniteSomewhere
axiom (forall t#0: DatatypeType :: 
  { _module.__default.IsFiniteSomewhere#requires(t#0) } 
  $Is(t#0, Tclass._module.Tree())
     ==> _module.__default.IsFiniteSomewhere#requires(t#0) == true);

// definition axiom for _module.__default.IsFiniteSomewhere (revealed)
axiom 45 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.IsFiniteSomewhere(t#0) } 
    _module.__default.IsFiniteSomewhere#canCall(t#0)
         || (45 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> _module.Tree.Node_q(t#0)
         && _module.__default.InfiniteEverywhere#canCall(_module.Tree.children(t#0))
         && _module.__default.IsFiniteSomewhere(t#0)
           == !_module.__default.InfiniteEverywhere($LS($LZ), _module.Tree.children(t#0)));

// definition axiom for _module.__default.IsFiniteSomewhere for all literals (revealed)
axiom 45 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    {:weight 3} { _module.__default.IsFiniteSomewhere(Lit(t#0)) } 
    _module.__default.IsFiniteSomewhere#canCall(Lit(t#0))
         || (45 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> _module.Tree.Node_q(Lit(t#0))
         && _module.__default.InfiniteEverywhere#canCall(Lit(_module.Tree.children(Lit(t#0))))
         && _module.__default.IsFiniteSomewhere(Lit(t#0))
           == !Lit(_module.__default.InfiniteEverywhere($LS($LZ), Lit(_module.Tree.children(Lit(t#0))))));

procedure CheckWellformed$$_module.__default.IsFiniteSomewhere(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()));
  free requires 45 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.IsFiniteSomewhere(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function IsFiniteSomewhere
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(101,10): initial state"} true;
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
        assume _module.Tree.Node_q(t#0);
        ##s#0 := _module.Tree.children(t#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.InfiniteEverywhere#canCall(_module.Tree.children(t#0));
        assume _module.__default.IsFiniteSomewhere(t#0)
           == !_module.__default.InfiniteEverywhere($LS($LZ), _module.Tree.children(t#0));
        assume _module.Tree.Node_q(t#0)
           && _module.__default.InfiniteEverywhere#canCall(_module.Tree.children(t#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.IsFiniteSomewhere(t#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.InfiniteEverywhere
function _module.__default.InfiniteEverywhere($ly: LayerType, s#0: DatatypeType) : bool;

function _module.__default.InfiniteEverywhere#canCall(s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.InfiniteEverywhere($LS($ly), s#0) } 
  _module.__default.InfiniteEverywhere($LS($ly), s#0)
     == _module.__default.InfiniteEverywhere($ly, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.InfiniteEverywhere(AsFuelBottom($ly), s#0) } 
  _module.__default.InfiniteEverywhere($ly, s#0)
     == _module.__default.InfiniteEverywhere($LZ, s#0));

// consequence axiom for _module.__default.InfiniteEverywhere
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.InfiniteEverywhere($ly, s#0) } 
    _module.__default.InfiniteEverywhere#canCall(s#0)
         || (10 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> true);

function _module.__default.InfiniteEverywhere#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.InfiniteEverywhere
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.InfiniteEverywhere#requires($ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
     ==> _module.__default.InfiniteEverywhere#requires($ly, s#0) == true);

// definition axiom for _module.__default.InfiniteEverywhere (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.InfiniteEverywhere($LS($ly), s#0) } 
    _module.__default.InfiniteEverywhere#canCall(s#0)
         || (10 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> (!_module.Stream.Nil_q(s#0)
           ==> (var tail#1 := _module.Stream.tail(s#0); 
            (var t#1 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              _module.Tree.Node_q(t#1)
                 && _module.__default.InfiniteEverywhere#canCall(_module.Tree.children(t#1))
                 && (_module.__default.InfiniteEverywhere($ly, _module.Tree.children(t#1))
                   ==> _module.__default.InfiniteEverywhere#canCall(tail#1)))))
         && _module.__default.InfiniteEverywhere($LS($ly), s#0)
           == (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#0 := _module.Stream.tail(s#0); 
              (var t#0 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                _module.__default.InfiniteEverywhere($ly, _module.Tree.children(t#0))
                   && _module.__default.InfiniteEverywhere($ly, tail#0)))));

// 1st prefix predicate axiom for _module.__default.InfiniteEverywhere_h
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.InfiniteEverywhere($LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && _module.__default.InfiniteEverywhere($LS($ly), s#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.InfiniteEverywhere_h($LS($ly), _k#0, s#0) } 
        _module.__default.InfiniteEverywhere_h($LS($ly), _k#0, s#0)));

// 2nd prefix predicate axiom
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.InfiniteEverywhere($LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && (forall _k#0: Box :: 
          { _module.__default.InfiniteEverywhere_h($LS($ly), _k#0, s#0) } 
          _module.__default.InfiniteEverywhere_h($LS($ly), _k#0, s#0))
       ==> _module.__default.InfiniteEverywhere($LS($ly), s#0));

// 3rd prefix predicate axiom
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, _k#0: Box :: 
    { _module.__default.InfiniteEverywhere_h($ly, _k#0, s#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())) && _k#0 == ORD#FromNat(0)
       ==> _module.__default.InfiniteEverywhere_h($ly, _k#0, s#0));

procedure CheckWellformed$$_module.__default.InfiniteEverywhere(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.InfiniteEverywhere(s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var t#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##s#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function InfiniteEverywhere
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(105,19): initial state"} true;
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
        if (s#0 == #_module.Stream.Nil())
        {
            assume _module.__default.InfiniteEverywhere($LS($LZ), s#0) == Lit(false);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.InfiniteEverywhere($LS($LZ), s#0), TBool);
        }
        else if (s#0 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Tree());
            assume $Is(_mcc#1#0, Tclass._module.Stream(Tclass._module.Tree()));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.Stream(Tclass._module.Tree()));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(Tclass._module.Tree()));
            assume tail#Z#0 == let#0#0#0;
            havoc t#Z#0;
            assume $Is(t#Z#0, Tclass._module.Tree());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Tree());
            assume t#Z#0 == let#1#0#0;
            assume _module.Tree.Node_q(t#Z#0);
            ##s#0 := _module.Tree.children(t#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.InfiniteEverywhere#canCall(_module.Tree.children(t#Z#0));
            if (_module.__default.InfiniteEverywhere($LS($LZ), _module.Tree.children(t#Z#0)))
            {
                ##s#1 := tail#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.InfiniteEverywhere#canCall(tail#Z#0);
            }

            assume _module.__default.InfiniteEverywhere($LS($LZ), s#0)
               == (_module.__default.InfiniteEverywhere($LS($LZ), _module.Tree.children(t#Z#0))
                 && _module.__default.InfiniteEverywhere($LS($LZ), tail#Z#0));
            assume _module.Tree.Node_q(t#Z#0)
               && _module.__default.InfiniteEverywhere#canCall(_module.Tree.children(t#Z#0))
               && (_module.__default.InfiniteEverywhere($LS($LZ), _module.Tree.children(t#Z#0))
                 ==> _module.__default.InfiniteEverywhere#canCall(tail#Z#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.InfiniteEverywhere($LS($LZ), s#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.InfiniteEverywhere#
function _module.__default.InfiniteEverywhere_h($ly: LayerType, _k#0: Box, s#0: DatatypeType) : bool;

function _module.__default.InfiniteEverywhere_h#canCall(_k#0: Box, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.InfiniteEverywhere_h($LS($ly), _k#0, s#0) } 
  _module.__default.InfiniteEverywhere_h($LS($ly), _k#0, s#0)
     == _module.__default.InfiniteEverywhere_h($ly, _k#0, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.InfiniteEverywhere_h(AsFuelBottom($ly), _k#0, s#0) } 
  _module.__default.InfiniteEverywhere_h($ly, _k#0, s#0)
     == _module.__default.InfiniteEverywhere_h($LZ, _k#0, s#0));

// consequence axiom for _module.__default.InfiniteEverywhere_h
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.InfiniteEverywhere_h($ly, _k#0, s#0) } 
    _module.__default.InfiniteEverywhere_h#canCall(_k#0, s#0)
         || (11 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> true);

function _module.__default.InfiniteEverywhere_h#requires(LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.InfiniteEverywhere_h
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.InfiniteEverywhere_h#requires($ly, _k#0, s#0) } 
  $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
     ==> _module.__default.InfiniteEverywhere_h#requires($ly, _k#0, s#0) == true);

// definition axiom for _module.__default.InfiniteEverywhere_h (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.InfiniteEverywhere_h($LS($ly), _k#0, s#0) } 
    _module.__default.InfiniteEverywhere_h#canCall(_k#0, s#0)
         || (11 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#3 := _module.Stream.tail(s#0); 
            (var t#3 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              _module.Tree.Node_q(t#3)
                 && _module.__default.InfiniteEverywhere_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#3))
                 && (_module.__default.InfiniteEverywhere_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#3))
                   ==> _module.__default.InfiniteEverywhere_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#3)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#4 := _module.Stream.tail(s#0); 
              (var t#4 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                _module.__default.InfiniteEverywhere_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#4))
                   && _module.__default.InfiniteEverywhere_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), tail#4)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.InfiniteEverywhere_h($ly, _k'#0, s#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.InfiniteEverywhere_h#canCall(_k'#0, s#0)))
         && _module.__default.InfiniteEverywhere_h($LS($ly), _k#0, s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#2 := _module.Stream.tail(s#0); 
                  (var t#2 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    _module.__default.InfiniteEverywhere_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#2))
                       && _module.__default.InfiniteEverywhere_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), tail#2)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.InfiniteEverywhere_h($ly, _k'#0, s#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.InfiniteEverywhere_h($ly, _k'#0, s#0)))));

// definition axiom for _module.__default.InfiniteEverywhere_h for decreasing-related literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.InfiniteEverywhere_h($LS($ly), Lit(_k#0), s#0) } 
    _module.__default.InfiniteEverywhere_h#canCall(Lit(_k#0), s#0)
         || (11 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#6 := _module.Stream.tail(s#0); 
            (var t#6 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              _module.Tree.Node_q(t#6)
                 && _module.__default.InfiniteEverywhere_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#6))
                 && (_module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#6))
                   ==> _module.__default.InfiniteEverywhere_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#6)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#7 := _module.Stream.tail(s#0); 
              (var t#7 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                _module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#7))
                   && _module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#7)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.InfiniteEverywhere_h($LS($ly), _k'#1, s#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.InfiniteEverywhere_h#canCall(_k'#1, s#0)))
         && _module.__default.InfiniteEverywhere_h($LS($ly), Lit(_k#0), s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#5 := _module.Stream.tail(s#0); 
                  (var t#5 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    _module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#5))
                       && _module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#5)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.InfiniteEverywhere_h($LS($ly), _k'#1, s#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.InfiniteEverywhere_h($LS($ly), _k'#1, s#0)))));

// definition axiom for _module.__default.InfiniteEverywhere_h for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.InfiniteEverywhere_h($LS($ly), Lit(_k#0), Lit(s#0)) } 
    _module.__default.InfiniteEverywhere_h#canCall(Lit(_k#0), Lit(s#0))
         || (11 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#9 := _module.Stream.tail(s#0); 
            (var t#9 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              _module.Tree.Node_q(t#9)
                 && _module.__default.InfiniteEverywhere_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#9))
                 && (_module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#9))
                   ==> _module.__default.InfiniteEverywhere_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#9)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#10 := _module.Stream.tail(s#0); 
              (var t#10 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                _module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#10))
                   && _module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#10)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.InfiniteEverywhere_h($LS($ly), _k'#2, s#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.InfiniteEverywhere_h#canCall(_k'#2, s#0)))
         && _module.__default.InfiniteEverywhere_h($LS($ly), Lit(_k#0), Lit(s#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#8 := _module.Stream.tail(s#0); 
                  (var t#8 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    _module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#8))
                       && _module.__default.InfiniteEverywhere_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#8)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.InfiniteEverywhere_h($LS($ly), _k'#2, s#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.InfiniteEverywhere_h($LS($ly), _k'#2, s#0)))));

// function declaration for _module._default.SkinnyTree
function _module.__default.SkinnyTree($ly: LayerType) : DatatypeType;

function _module.__default.SkinnyTree#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.SkinnyTree($LS($ly)) } 
  _module.__default.SkinnyTree($LS($ly)) == _module.__default.SkinnyTree($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.SkinnyTree(AsFuelBottom($ly)) } 
  _module.__default.SkinnyTree($ly) == _module.__default.SkinnyTree($LZ));

// consequence axiom for _module.__default.SkinnyTree
axiom 46 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.SkinnyTree($ly) } 
    _module.__default.SkinnyTree#canCall() || 46 != $FunctionContextHeight
       ==> $Is(_module.__default.SkinnyTree($ly), Tclass._module.Tree()));

function _module.__default.SkinnyTree#requires(LayerType) : bool;

// #requires axiom for _module.__default.SkinnyTree
axiom (forall $ly: LayerType :: 
  { _module.__default.SkinnyTree#requires($ly) } 
  _module.__default.SkinnyTree#requires($ly) == true);

// definition axiom for _module.__default.SkinnyTree (revealed)
axiom 46 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.SkinnyTree($LS($ly)) } 
    _module.__default.SkinnyTree#canCall() || 46 != $FunctionContextHeight
       ==> _module.__default.SkinnyTree#canCall()
         && _module.__default.SkinnyTree($LS($ly))
           == Lit(#_module.Tree.Node(Lit(#_module.Stream.Cons($Box(Lit(_module.__default.SkinnyTree($ly))), Lit(#_module.Stream.Nil()))))));

procedure CheckWellformed$$_module.__default.SkinnyTree();
  free requires 46 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.SkinnyTree()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function SkinnyTree
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(115,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.SkinnyTree($LS($LZ)), Tclass._module.Tree());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.SkinnyTree#canCall();
        assume _module.Tree.Node_q(Lit(_module.__default.SkinnyTree($LS($LZ))));
        assume _module.__default.SkinnyTree($LS($LZ))
           == Lit(#_module.Tree.Node(Lit(#_module.Stream.Cons($Box(Lit(_module.__default.SkinnyTree($LS($LZ)))), Lit(#_module.Stream.Nil())))));
        assume _module.__default.SkinnyTree#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.SkinnyTree($LS($LZ)), Tclass._module.Tree());
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.Proposition1();
  free requires 66 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Proposition1();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SkinnyTree#canCall()
     && _module.__default.IsFiniteSomewhere#canCall(Lit(_module.__default.SkinnyTree($LS($LZ))))
     && (Lit(_module.__default.IsFiniteSomewhere(Lit(_module.__default.SkinnyTree($LS($LZ)))))
       ==> _module.__default.SkinnyTree#canCall()
         && _module.__default.HasBoundedHeight#canCall(Lit(_module.__default.SkinnyTree($LS($LZ)))));
  free ensures _module.__default.IsFiniteSomewhere#canCall(Lit(_module.__default.SkinnyTree($LS($LZ))))
     && 
    Lit(_module.__default.IsFiniteSomewhere(Lit(_module.__default.SkinnyTree($LS($LZ)))))
     && !Lit(_module.__default.InfiniteEverywhere($LS($LZ), 
        Lit(_module.Tree.children(Lit(_module.__default.SkinnyTree($LS($LZ)))))));
  ensures !Lit(_module.__default.HasBoundedHeight(Lit(_module.__default.SkinnyTree($LS($LS($LZ))))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Proposition1() returns ($_reverifyPost: bool);
  free requires 66 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.SkinnyTree#canCall()
     && _module.__default.IsFiniteSomewhere#canCall(Lit(_module.__default.SkinnyTree($LS($LZ))))
     && (Lit(_module.__default.IsFiniteSomewhere(Lit(_module.__default.SkinnyTree($LS($LZ)))))
       ==> _module.__default.SkinnyTree#canCall()
         && _module.__default.HasBoundedHeight#canCall(Lit(_module.__default.SkinnyTree($LS($LZ)))));
  ensures _module.__default.IsFiniteSomewhere#canCall(Lit(_module.__default.SkinnyTree($LS($LZ))))
     ==> Lit(_module.__default.IsFiniteSomewhere(Lit(_module.__default.SkinnyTree($LS($LZ)))))
       || !Lit(_module.__default.InfiniteEverywhere($LS($LS($LZ)), 
          Lit(_module.Tree.children(Lit(_module.__default.SkinnyTree($LS($LS($LZ))))))));
  ensures !Lit(_module.__default.HasBoundedHeight(Lit(_module.__default.SkinnyTree($LS($LS($LZ))))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Proposition1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var ##s#0: DatatypeType;
  var ##n#0: int;

    // AddMethodImpl: Proposition1, Impl$$_module.__default.Proposition1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(121,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(122,3)
    // Begin Comprehension WF check
    havoc n#0;
    if (LitInt(0) <= n#0)
    {
        if (LitInt(0) <= n#0)
        {
            assume _module.__default.SkinnyTree#canCall();
            assume _module.Tree.Node_q(Lit(_module.__default.SkinnyTree($LS($LZ))));
            assume _module.Tree.Node_q(Lit(_module.__default.SkinnyTree($LS($LZ))));
            ##s#0 := Lit(_module.Tree.children(Lit(_module.__default.SkinnyTree($LS($LZ)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(Lit(_module.Tree.children(Lit(_module.__default.SkinnyTree($LS($LZ))))), n#0);
        }
    }

    // End Comprehension WF check
    assume (forall n#1: int :: 
      { _module.__default.LowerThan($LS($LZ), _module.Tree.children(_module.__default.SkinnyTree($LS($LZ))), n#1) } 
      LitInt(0) <= n#1
         ==> 
        LitInt(0) <= n#1
         ==> _module.__default.SkinnyTree#canCall()
           && _module.Tree.Node_q(Lit(_module.__default.SkinnyTree($LS($LZ))))
           && _module.__default.LowerThan#canCall(Lit(_module.Tree.children(Lit(_module.__default.SkinnyTree($LS($LZ))))), n#1));
    assert {:subsumption 0} (forall n#1: int :: 
      { _module.__default.LowerThan($LS($LS($LZ)), 
          _module.Tree.children(_module.__default.SkinnyTree($LS($LS($LZ)))), 
          n#1) } 
      LitInt(0) <= n#1
           && (forall n$ih#0#0: int :: 
            { _module.__default.LowerThan($LS($LZ), 
                _module.Tree.children(_module.__default.SkinnyTree($LS($LZ))), 
                n$ih#0#0) } 
            LitInt(0) <= n$ih#0#0
               ==> 
              0 <= n$ih#0#0 && n$ih#0#0 < n#1
               ==> 
              LitInt(0) <= n$ih#0#0
               ==> !_module.__default.LowerThan($LS($LZ), 
                Lit(_module.Tree.children(Lit(_module.__default.SkinnyTree($LS($LZ))))), 
                n$ih#0#0))
           && true
         ==> 
        LitInt(0) <= n#1
         ==> !_module.__default.LowerThan($LS($LS($LZ)), 
          Lit(_module.Tree.children(Lit(_module.__default.SkinnyTree($LS($LS($LZ)))))), 
          n#1));
    assume (forall n#1: int :: 
      {:induction} {:_induction n#1} { _module.__default.LowerThan($LS($LZ), _module.Tree.children(_module.__default.SkinnyTree($LS($LZ))), n#1) } 
      LitInt(0) <= n#1
         ==> 
        LitInt(0) <= n#1
         ==> !_module.__default.LowerThan($LS($LZ), 
          Lit(_module.Tree.children(Lit(_module.__default.SkinnyTree($LS($LZ))))), 
          n#1));
}



procedure CheckWellformed$$_module.__default.Theorem0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0));
  free requires 48 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0));
  // user-defined preconditions
  requires _module.__default.HasBoundedHeight#canCall(t#0)
     ==> _module.__default.HasBoundedHeight(t#0)
       || (exists n#0: int :: 
        { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0) } 
        LitInt(0) <= n#0
           && 
          LitInt(0) <= n#0
           && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsFiniteSomewhere#canCall(t#0);
  free ensures _module.__default.IsFiniteSomewhere#canCall(t#0)
     && 
    _module.__default.IsFiniteSomewhere(t#0)
     && !_module.__default.InfiniteEverywhere($LS($LZ), _module.Tree.children(t#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Theorem0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0))
   returns ($_reverifyPost: bool);
  free requires 48 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.HasBoundedHeight#canCall(t#0)
     && 
    _module.__default.HasBoundedHeight(t#0)
     && (exists n#1: int :: 
      { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#1) } 
      LitInt(0) <= n#1
         && 
        LitInt(0) <= n#1
         && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsFiniteSomewhere#canCall(t#0);
  ensures _module.__default.IsFiniteSomewhere#canCall(t#0)
     ==> _module.__default.IsFiniteSomewhere(t#0)
       || !_module.__default.InfiniteEverywhere($LS($LS($LZ)), _module.Tree.children(t#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Theorem0(t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#2: int where LitInt(0) <= n#2;
  var n#3: int;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var k#0: int where LitInt(0) <= k#0;
  var $rhs##0: int where LitInt(0) <= $rhs##0;
  var s##0: DatatypeType;
  var n##0: int;

    // AddMethodImpl: Theorem0, Impl$$_module.__default.Theorem0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(130,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(131,9)
    havoc n#3;
    if (LitInt(0) <= n#3)
    {
        if (LitInt(0) <= n#3)
        {
            assume _module.Tree.Node_q(t#0);
            ##s#0 := _module.Tree.children(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#0 := n#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#3);
        }

        assume LitInt(0) <= n#3
           ==> _module.Tree.Node_q(t#0)
             && _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#3);
    }

    assert ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), LitInt(0)))
       || 
      ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), LitInt(0)))
       || 
      ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), LitInt(0)))
       || (exists $as#n0#0: int :: 
        LitInt(0) <= $as#n0#0
           && 
          LitInt(0) <= $as#n0#0
           && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), $as#n0#0));
    havoc n#2;
    assume LitInt(0) <= n#2
       && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#2);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(131,45)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(137,19)
    assume true;
    // TrCallStmt: Adding lhs with type nat
    // TrCallStmt: Before ProcessCallStmt
    assume _module.Tree.Node_q(t#0);
    assume _module.Tree.Node_q(t#0);
    // ProcessCallStmt: CheckSubrange
    s##0 := _module.Tree.children(t#0);
    assume true;
    // ProcessCallStmt: CheckSubrange
    n##0 := n#2;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.__default.FindNil(s##0, n##0);
    // TrCallStmt: After ProcessCallStmt
    k#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(137,33)"} true;
}



procedure CheckWellformed$$_module.__default.FindNil(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0)
   returns (k#0: int where LitInt(0) <= k#0);
  free requires 47 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.FindNil(s#0: DatatypeType, n#0: int) returns (k#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var newtype$check#0: int;
  var ##_k#0: Box;
  var ##s#1: DatatypeType;

    // AddMethodImpl: FindNil, CheckWellformed$$_module.__default.FindNil
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(139,6): initial state"} true;
    ##s#0 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.LowerThan#canCall(s#0, n#0);
    assume _module.__default.LowerThan($LS($LZ), s#0, n#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    havoc k#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(141,10): post-state"} true;
    newtype$check#0 := k#0;
    assert 0 <= newtype$check#0;
    ##_k#0 := ORD#FromNat(k#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##_k#0, TORDINAL, $Heap);
    ##s#1 := s#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
    assume _module.__default.InfiniteEverywhere_h#canCall(ORD#FromNat(k#0), s#0);
    assume !_module.__default.InfiniteEverywhere_h($LS($LZ), ORD#FromNat(k#0), s#0);
}



procedure Call$$_module.__default.FindNil(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0)
   returns (k#0: int where LitInt(0) <= k#0);
  // user-defined preconditions
  requires _module.__default.LowerThan($LS($LS($LZ)), s#0, n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.InfiniteEverywhere_h#canCall(ORD#FromNat(k#0), s#0);
  ensures !_module.__default.InfiniteEverywhere_h($LS($LS($LZ)), ORD#FromNat(k#0), s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.FindNil(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0)
   returns (k#0: int where LitInt(0) <= k#0, $_reverifyPost: bool);
  free requires 47 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.LowerThan($LS($LS($LZ)), s#0, n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.InfiniteEverywhere_h#canCall(ORD#FromNat(k#0), s#0);
  ensures !_module.__default.InfiniteEverywhere_h($LS($LS($LZ)), ORD#FromNat(k#0), s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.FindNil(s#0: DatatypeType, n#0: int) returns (k#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0_0: DatatypeType;
  var _mcc#1#0_0: DatatypeType;
  var t#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var $rhs##0_0: int where LitInt(0) <= $rhs##0_0;
  var s##0_0: DatatypeType;
  var n##0_0: int;

    // AddMethodImpl: FindNil, Impl$$_module.__default.FindNil
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(142,0): initial state"} true;
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (s#0 == #_module.Stream.Nil())
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(144,19)
        assume true;
        assume true;
        assert $Is(LitInt(1), Tclass._System.nat());
        k#0 := LitInt(1);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(144,22)"} true;
    }
    else if (s#0 == #_module.Stream.Cons($Box(_mcc#0#0_0), _mcc#1#0_0))
    {
        assume $Is(_mcc#0#0_0, Tclass._module.Tree());
        assume $Is(_mcc#1#0_0, Tclass._module.Stream(Tclass._module.Tree()));
        havoc t#0_0;
        assume $Is(t#0_0, Tclass._module.Tree())
           && $IsAlloc(t#0_0, Tclass._module.Tree(), $Heap);
        assume let#0_0#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Tree());
        assume t#0_0 == let#0_0#0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(146,16)
        assume true;
        // TrCallStmt: Adding lhs with type nat
        // TrCallStmt: Before ProcessCallStmt
        assume _module.Tree.Node_q(t#0_0);
        assume _module.Tree.Node_q(t#0_0);
        // ProcessCallStmt: CheckSubrange
        s##0_0 := _module.Tree.children(t#0_0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0 - 1, Tclass._System.nat());
        n##0_0 := n#0 - 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= n#0 || n##0_0 == n#0;
        assert n##0_0 < n#0;
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$_module.__default.FindNil(s##0_0, n##0_0);
        // TrCallStmt: After ProcessCallStmt
        k#0 := $rhs##0_0;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(146,32)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(147,6)
        assume true;
        assume true;
        assert $Is(k#0 + 1, Tclass._System.nat());
        k#0 := k#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(147,13)"} true;
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.HasFiniteHeightEverywhere_Bad
function _module.__default.HasFiniteHeightEverywhere__Bad(t#0: DatatypeType) : bool;

function _module.__default.HasFiniteHeightEverywhere__Bad#canCall(t#0: DatatypeType) : bool;

// consequence axiom for _module.__default.HasFiniteHeightEverywhere__Bad
axiom 49 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.HasFiniteHeightEverywhere__Bad(t#0) } 
    _module.__default.HasFiniteHeightEverywhere__Bad#canCall(t#0)
         || (49 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> true);

function _module.__default.HasFiniteHeightEverywhere__Bad#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.HasFiniteHeightEverywhere__Bad
axiom (forall t#0: DatatypeType :: 
  { _module.__default.HasFiniteHeightEverywhere__Bad#requires(t#0) } 
  $Is(t#0, Tclass._module.Tree())
     ==> _module.__default.HasFiniteHeightEverywhere__Bad#requires(t#0) == true);

// definition axiom for _module.__default.HasFiniteHeightEverywhere__Bad (revealed)
axiom 49 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.HasFiniteHeightEverywhere__Bad(t#0) } 
    _module.__default.HasFiniteHeightEverywhere__Bad#canCall(t#0)
         || (49 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> _module.Tree.Node_q(t#0)
         && _module.__default.InfiniteHeightSomewhere__Bad#canCall(_module.Tree.children(t#0))
         && _module.__default.HasFiniteHeightEverywhere__Bad(t#0)
           == !_module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), _module.Tree.children(t#0)));

// definition axiom for _module.__default.HasFiniteHeightEverywhere__Bad for all literals (revealed)
axiom 49 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    {:weight 3} { _module.__default.HasFiniteHeightEverywhere__Bad(Lit(t#0)) } 
    _module.__default.HasFiniteHeightEverywhere__Bad#canCall(Lit(t#0))
         || (49 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> _module.Tree.Node_q(Lit(t#0))
         && _module.__default.InfiniteHeightSomewhere__Bad#canCall(Lit(_module.Tree.children(Lit(t#0))))
         && _module.__default.HasFiniteHeightEverywhere__Bad(Lit(t#0))
           == !Lit(_module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), Lit(_module.Tree.children(Lit(t#0))))));

procedure CheckWellformed$$_module.__default.HasFiniteHeightEverywhere__Bad(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()));
  free requires 49 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.HasFiniteHeightEverywhere__Bad(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function HasFiniteHeightEverywhere_Bad
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(155,10): initial state"} true;
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
        assume _module.Tree.Node_q(t#0);
        ##s#0 := _module.Tree.children(t#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.InfiniteHeightSomewhere__Bad#canCall(_module.Tree.children(t#0));
        assume _module.__default.HasFiniteHeightEverywhere__Bad(t#0)
           == !_module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), _module.Tree.children(t#0));
        assume _module.Tree.Node_q(t#0)
           && _module.__default.InfiniteHeightSomewhere__Bad#canCall(_module.Tree.children(t#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.HasFiniteHeightEverywhere__Bad(t#0), TBool);
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.InfiniteHeightSomewhere_Bad
function _module.__default.InfiniteHeightSomewhere__Bad($ly: LayerType, s#0: DatatypeType) : bool;

function _module.__default.InfiniteHeightSomewhere__Bad#canCall(s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.InfiniteHeightSomewhere__Bad($LS($ly), s#0) } 
  _module.__default.InfiniteHeightSomewhere__Bad($LS($ly), s#0)
     == _module.__default.InfiniteHeightSomewhere__Bad($ly, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.InfiniteHeightSomewhere__Bad(AsFuelBottom($ly), s#0) } 
  _module.__default.InfiniteHeightSomewhere__Bad($ly, s#0)
     == _module.__default.InfiniteHeightSomewhere__Bad($LZ, s#0));

// consequence axiom for _module.__default.InfiniteHeightSomewhere__Bad
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.InfiniteHeightSomewhere__Bad($ly, s#0) } 
    _module.__default.InfiniteHeightSomewhere__Bad#canCall(s#0)
         || (12 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> true);

function _module.__default.InfiniteHeightSomewhere__Bad#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.InfiniteHeightSomewhere__Bad
axiom (forall $ly: LayerType, s#0: DatatypeType :: 
  { _module.__default.InfiniteHeightSomewhere__Bad#requires($ly, s#0) } 
  $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
     ==> _module.__default.InfiniteHeightSomewhere__Bad#requires($ly, s#0) == true);

// definition axiom for _module.__default.InfiniteHeightSomewhere__Bad (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.InfiniteHeightSomewhere__Bad($LS($ly), s#0) } 
    _module.__default.InfiniteHeightSomewhere__Bad#canCall(s#0)
         || (12 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> (!_module.Stream.Nil_q(s#0)
           ==> (var tail#1 := _module.Stream.tail(s#0); 
            (var t#1 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              _module.Tree.Node_q(t#1)
                 && _module.__default.InfiniteHeightSomewhere__Bad#canCall(_module.Tree.children(t#1))
                 && (!_module.__default.InfiniteHeightSomewhere__Bad($ly, _module.Tree.children(t#1))
                   ==> _module.__default.InfiniteHeightSomewhere__Bad#canCall(tail#1)))))
         && _module.__default.InfiniteHeightSomewhere__Bad($LS($ly), s#0)
           == (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#0 := _module.Stream.tail(s#0); 
              (var t#0 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                _module.__default.InfiniteHeightSomewhere__Bad($ly, _module.Tree.children(t#0))
                   || _module.__default.InfiniteHeightSomewhere__Bad($ly, tail#0)))));

// 1st prefix predicate axiom for _module.__default.InfiniteHeightSomewhere__Bad_h
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.InfiniteHeightSomewhere__Bad($LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && _module.__default.InfiniteHeightSomewhere__Bad($LS($ly), s#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k#0, s#0) } 
        _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k#0, s#0)));

// 2nd prefix predicate axiom
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType :: 
    { _module.__default.InfiniteHeightSomewhere__Bad($LS($ly), s#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && (forall _k#0: Box :: 
          { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k#0, s#0) } 
          _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k#0, s#0))
       ==> _module.__default.InfiniteHeightSomewhere__Bad($LS($ly), s#0));

// 3rd prefix predicate axiom
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, _k#0: Box :: 
    { _module.__default.InfiniteHeightSomewhere__Bad_h($ly, _k#0, s#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())) && _k#0 == ORD#FromNat(0)
       ==> _module.__default.InfiniteHeightSomewhere__Bad_h($ly, _k#0, s#0));

procedure CheckWellformed$$_module.__default.InfiniteHeightSomewhere__Bad(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.InfiniteHeightSomewhere__Bad(s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var t#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##s#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function InfiniteHeightSomewhere_Bad
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(159,19): initial state"} true;
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
        if (s#0 == #_module.Stream.Nil())
        {
            assume _module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), s#0) == Lit(false);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), s#0), TBool);
        }
        else if (s#0 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Tree());
            assume $Is(_mcc#1#0, Tclass._module.Stream(Tclass._module.Tree()));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.Stream(Tclass._module.Tree()));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(Tclass._module.Tree()));
            assume tail#Z#0 == let#0#0#0;
            havoc t#Z#0;
            assume $Is(t#Z#0, Tclass._module.Tree());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Tree());
            assume t#Z#0 == let#1#0#0;
            assume _module.Tree.Node_q(t#Z#0);
            ##s#0 := _module.Tree.children(t#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.InfiniteHeightSomewhere__Bad#canCall(_module.Tree.children(t#Z#0));
            if (!_module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), _module.Tree.children(t#Z#0)))
            {
                ##s#1 := tail#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.InfiniteHeightSomewhere__Bad#canCall(tail#Z#0);
            }

            assume _module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), s#0)
               == (_module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), _module.Tree.children(t#Z#0))
                 || _module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), tail#Z#0));
            assume _module.Tree.Node_q(t#Z#0)
               && _module.__default.InfiniteHeightSomewhere__Bad#canCall(_module.Tree.children(t#Z#0))
               && (!_module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), _module.Tree.children(t#Z#0))
                 ==> _module.__default.InfiniteHeightSomewhere__Bad#canCall(tail#Z#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.InfiniteHeightSomewhere__Bad($LS($LZ), s#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.InfiniteHeightSomewhere_Bad#
function _module.__default.InfiniteHeightSomewhere__Bad_h($ly: LayerType, _k#0: Box, s#0: DatatypeType) : bool;

function _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k#0: Box, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k#0, s#0) } 
  _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k#0, s#0)
     == _module.__default.InfiniteHeightSomewhere__Bad_h($ly, _k#0, s#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.InfiniteHeightSomewhere__Bad_h(AsFuelBottom($ly), _k#0, s#0) } 
  _module.__default.InfiniteHeightSomewhere__Bad_h($ly, _k#0, s#0)
     == _module.__default.InfiniteHeightSomewhere__Bad_h($LZ, _k#0, s#0));

// consequence axiom for _module.__default.InfiniteHeightSomewhere__Bad_h
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.InfiniteHeightSomewhere__Bad_h($ly, _k#0, s#0) } 
    _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k#0, s#0)
         || (13 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> true);

function _module.__default.InfiniteHeightSomewhere__Bad_h#requires(LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.InfiniteHeightSomewhere__Bad_h
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
  { _module.__default.InfiniteHeightSomewhere__Bad_h#requires($ly, _k#0, s#0) } 
  $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
     ==> _module.__default.InfiniteHeightSomewhere__Bad_h#requires($ly, _k#0, s#0)
       == true);

// definition axiom for _module.__default.InfiniteHeightSomewhere__Bad_h (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k#0, s#0) } 
    _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k#0, s#0)
         || (13 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#3 := _module.Stream.tail(s#0); 
            (var t#3 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              _module.Tree.Node_q(t#3)
                 && _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#3))
                 && (!_module.__default.InfiniteHeightSomewhere__Bad_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#3))
                   ==> _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#3)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#4 := _module.Stream.tail(s#0); 
              (var t#4 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                _module.__default.InfiniteHeightSomewhere__Bad_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#4))
                   || _module.__default.InfiniteHeightSomewhere__Bad_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), tail#4)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.InfiniteHeightSomewhere__Bad_h($ly, _k'#0, s#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k'#0, s#0)))
         && _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k#0, s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#2 := _module.Stream.tail(s#0); 
                  (var t#2 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    _module.__default.InfiniteHeightSomewhere__Bad_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#2))
                       || _module.__default.InfiniteHeightSomewhere__Bad_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), tail#2)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.InfiniteHeightSomewhere__Bad_h($ly, _k'#0, s#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.InfiniteHeightSomewhere__Bad_h($ly, _k'#0, s#0)))));

// definition axiom for _module.__default.InfiniteHeightSomewhere__Bad_h for decreasing-related literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), Lit(_k#0), s#0) } 
    _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(Lit(_k#0), s#0)
         || (13 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#6 := _module.Stream.tail(s#0); 
            (var t#6 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              _module.Tree.Node_q(t#6)
                 && _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#6))
                 && (!_module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#6))
                   ==> _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#6)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#7 := _module.Stream.tail(s#0); 
              (var t#7 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#7))
                   || _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#7)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k'#1, s#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k'#1, s#0)))
         && _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), Lit(_k#0), s#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#5 := _module.Stream.tail(s#0); 
                  (var t#5 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#5))
                       || _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#5)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k'#1, s#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k'#1, s#0)))));

// definition axiom for _module.__default.InfiniteHeightSomewhere__Bad_h for all literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), Lit(_k#0), Lit(s#0)) } 
    _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(Lit(_k#0), Lit(s#0))
         || (13 != $FunctionContextHeight
           && $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.Stream.Nil_q(s#0)
           ==> (var tail#9 := _module.Stream.tail(s#0); 
            (var t#9 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
              _module.Tree.Node_q(t#9)
                 && _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#9))
                 && (!_module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#9))
                   ==> _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), tail#9)))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(s#0)
             then false
             else (var tail#10 := _module.Stream.tail(s#0); 
              (var t#10 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#10))
                   || _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#10)))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k'#2, s#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k'#2, s#0)))
         && _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), Lit(_k#0), Lit(s#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(s#0)
                 then false
                 else (var tail#8 := _module.Stream.tail(s#0); 
                  (var t#8 := $Unbox(_module.Stream.head(s#0)): DatatypeType; 
                    _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#8))
                       || _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), tail#8)))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k'#2, s#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.InfiniteHeightSomewhere__Bad_h($LS($ly), _k'#2, s#0)))));

// function declaration for _module._default.ATree
function _module.__default.ATree() : DatatypeType;

function _module.__default.ATree#canCall() : bool;

// consequence axiom for _module.__default.ATree
axiom 50 <= $FunctionContextHeight
   ==> 
  _module.__default.ATree#canCall() || 50 != $FunctionContextHeight
   ==> $Is(_module.__default.ATree(), Tclass._module.Tree());

function _module.__default.ATree#requires() : bool;

// #requires axiom for _module.__default.ATree
axiom _module.__default.ATree#requires() == true;

// definition axiom for _module.__default.ATree (revealed)
axiom 50 <= $FunctionContextHeight
   ==> 
  _module.__default.ATree#canCall() || 50 != $FunctionContextHeight
   ==> _module.__default.ATreeChildren#canCall()
     && _module.__default.ATree()
       == Lit(#_module.Tree.Node(Lit(_module.__default.ATreeChildren($LS($LZ)))));

// definition axiom for _module.__default.ATree for all literals (revealed)
axiom 50 <= $FunctionContextHeight
   ==> 
  _module.__default.ATree#canCall() || 50 != $FunctionContextHeight
   ==> _module.__default.ATreeChildren#canCall()
     && _module.__default.ATree()
       == Lit(#_module.Tree.Node(Lit(_module.__default.ATreeChildren($LS($LZ)))));

procedure CheckWellformed$$_module.__default.ATree();
  free requires 50 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ATree()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ATree
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(173,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ATree(), Tclass._module.Tree());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.ATreeChildren#canCall();
        assume _module.__default.ATree()
           == Lit(#_module.Tree.Node(Lit(_module.__default.ATreeChildren($LS($LZ)))));
        assume _module.__default.ATreeChildren#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ATree(), Tclass._module.Tree());
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.ATreeChildren
function _module.__default.ATreeChildren($ly: LayerType) : DatatypeType;

function _module.__default.ATreeChildren#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.ATreeChildren($LS($ly)) } 
  _module.__default.ATreeChildren($LS($ly))
     == _module.__default.ATreeChildren($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.ATreeChildren(AsFuelBottom($ly)) } 
  _module.__default.ATreeChildren($ly) == _module.__default.ATreeChildren($LZ));

// consequence axiom for _module.__default.ATreeChildren
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.ATreeChildren($ly) } 
    _module.__default.ATreeChildren#canCall() || 14 != $FunctionContextHeight
       ==> $Is(_module.__default.ATreeChildren($ly), 
        Tclass._module.Stream(Tclass._module.Tree())));

function _module.__default.ATreeChildren#requires(LayerType) : bool;

// #requires axiom for _module.__default.ATreeChildren
axiom (forall $ly: LayerType :: 
  { _module.__default.ATreeChildren#requires($ly) } 
  _module.__default.ATreeChildren#requires($ly) == true);

// definition axiom for _module.__default.ATreeChildren (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.ATreeChildren($LS($ly)) } 
    _module.__default.ATreeChildren#canCall() || 14 != $FunctionContextHeight
       ==> _module.__default.ATreeChildren#canCall()
         && _module.__default.ATreeChildren($LS($ly))
           == Lit(#_module.Stream.Cons($Box(Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil())))), 
              Lit(_module.__default.ATreeChildren($ly)))));

procedure CheckWellformed$$_module.__default.ATreeChildren();
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ATreeChildren()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ATreeChildren
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(177,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ATreeChildren($LS($LZ)), 
          Tclass._module.Stream(Tclass._module.Tree()));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.ATreeChildren#canCall();
        assume _module.__default.ATreeChildren($LS($LZ))
           == Lit(#_module.Stream.Cons($Box(Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil())))), 
              Lit(_module.__default.ATreeChildren($LS($LZ)))));
        assume _module.__default.ATreeChildren#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ATreeChildren($LS($LZ)), 
          Tclass._module.Stream(Tclass._module.Tree()));
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.Proposition2();
  free requires 67 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Proposition2();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ATree#canCall()
     && _module.__default.HasFiniteHeightEverywhere__Bad#canCall(Lit(_module.__default.ATree()));
  ensures !Lit(_module.__default.HasFiniteHeightEverywhere__Bad(Lit(_module.__default.ATree())));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Proposition2() returns ($_reverifyPost: bool);
  free requires 67 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ATree#canCall()
     && _module.__default.HasFiniteHeightEverywhere__Bad#canCall(Lit(_module.__default.ATree()));
  ensures !Lit(_module.__default.HasFiniteHeightEverywhere__Bad(Lit(_module.__default.ATree())));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Proposition2() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s##0: DatatypeType;

    // AddMethodImpl: Proposition2, Impl$$_module.__default.Proposition2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(183,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(184,22)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Proposition2__Lemma0();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(184,23)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(185,22)
    // TrCallStmt: Before ProcessCallStmt
    assume _module.__default.ATreeChildren#canCall();
    assume _module.__default.ATreeChildren#canCall();
    // ProcessCallStmt: CheckSubrange
    s##0 := Lit(_module.__default.ATreeChildren($LS($LZ)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Proposition2__Lemma1(s##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(185,38)"} true;
}



procedure CheckWellformed$$_module.__default.Proposition2__Lemma0();
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Proposition2__Lemma0();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ATreeChildren#canCall()
     && _module.__default.IsNeverEndingStream#canCall(Tclass._module.Tree(), Lit(_module.__default.ATreeChildren($LS($LZ))));
  ensures Lit(_module.__default.IsNeverEndingStream(Tclass._module.Tree(), 
      $LS($LS($LZ)), 
      Lit(_module.__default.ATreeChildren($LS($LS($LZ))))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} CoCall$$_module.__default.Proposition2__Lemma0_h(_k#0: Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ATreeChildren#canCall()
     && _module.__default.IsNeverEndingStream_h#canCall(Tclass._module.Tree(), _k#0, Lit(_module.__default.ATreeChildren($LS($LZ))));
  ensures _module.__default.IsNeverEndingStream_h(Tclass._module.Tree(), 
    $LS($LS($LZ)), 
    _k#0, 
    Lit(_module.__default.ATreeChildren($LS($LS($LZ)))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} Impl$$_module.__default.Proposition2__Lemma0_h(_k#0: Box) returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ATreeChildren#canCall()
     && _module.__default.IsNeverEndingStream_h#canCall(Tclass._module.Tree(), _k#0, Lit(_module.__default.ATreeChildren($LS($LZ))));
  ensures _module.__default.IsNeverEndingStream_h(Tclass._module.Tree(), 
    $LS($LS($LZ)), 
    _k#0, 
    Lit(_module.__default.ATreeChildren($LS($LS($LZ)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0} Impl$$_module.__default.Proposition2__Lemma0_h(_k#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Proposition2_Lemma0#, Impl$$_module.__default.Proposition2__Lemma0_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(187,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box :: 
      Lit(true) && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.IsNeverEndingStream_h(Tclass._module.Tree(), 
          $LS($LZ), 
          $ih#_k0#0, 
          Lit(_module.__default.ATreeChildren($LS($LZ)))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(189,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(187,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box :: 
          ORD#Less(_k'#0, _k#0)
             ==> _module.__default.IsNeverEndingStream_h(Tclass._module.Tree(), 
              $LS($LZ), 
              _k'#0, 
              Lit(_module.__default.ATreeChildren($LS($LZ)))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(187,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Proposition2__Lemma1(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Proposition2__Lemma1(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0));
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(Tclass._module.Tree(), $LS($LS($LZ)), s#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.InfiniteHeightSomewhere__Bad#canCall(s#0);
  ensures _module.__default.InfiniteHeightSomewhere__Bad($LS($LS($LZ)), s#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} CoCall$$_module.__default.Proposition2__Lemma1_h(_k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#1));
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(Tclass._module.Tree(), $LS($LS($LZ)), s#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k#0, s#1);
  ensures _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LS($LZ)), _k#0, s#1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1} Impl$$_module.__default.Proposition2__Lemma1_h(_k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#1))
   returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(Tclass._module.Tree(), $LS($LS($LZ)), s#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k#0, s#1);
  ensures _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LS($LZ)), _k#0, s#1);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1} Impl$$_module.__default.Proposition2__Lemma1_h(_k#0: Box, s#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##_k#0: Box;
  var ##s#2: DatatypeType;
  var ##_k#1: Box;
  var ##s#3: DatatypeType;
  var ##_k#2: Box;
  var ##s#4: DatatypeType;
  var ##_k#3: Box;
  var ##s#5: DatatypeType;
  var ##_k#4: Box;
  var ##s#6: DatatypeType;
  var ##_k#5: Box;
  var ##s#7: DatatypeType;
  var ##_k#6: Box;
  var ##s#8: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Proposition2_Lemma1#, Impl$$_module.__default.Proposition2__Lemma1_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(191,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(Tclass._module.Tree()))
           && _module.__default.IsNeverEndingStream(Tclass._module.Tree(), $LS($LZ), $ih#s0#0)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), $ih#_k0#0, $ih#s0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(194,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assert _module.Stream.Cons_q(s#1);
            ##_k#6 := ORD#Minus(_k#0, ORD#FromNat(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#6, TORDINAL, $Heap);
            ##s#8 := _module.Stream.tail(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#8, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1));
            assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            ##_k#3 := _k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#3, TORDINAL, $Heap);
            ##s#5 := s#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#5, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k#0, s#1);
            assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(_k#0, s#1);
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assert _module.Stream.Cons_q(s#1);
            assume _module.Tree.Node_q($Unbox(_module.Stream.head(s#1)): DatatypeType);
            ##_k#4 := ORD#Minus(_k#0, ORD#FromNat(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#4, TORDINAL, $Heap);
            ##s#6 := _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#6, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType));
            if (!_module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType)))
            {
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assert _module.Stream.Cons_q(s#1);
                ##_k#5 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#5, TORDINAL, $Heap);
                ##s#7 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#7, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1));
            }

            assume _module.Tree.Node_q($Unbox(_module.Stream.head(s#1)): DatatypeType)
               && _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType))
               && (!_module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType))
                 ==> _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1)));
            // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            assert {:subsumption 0} _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LS($LZ)), _k#0, s#1)
               == (_module.__default.InfiniteHeightSomewhere__Bad_h($LS($LS($LZ)), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType))
                 || _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LS($LZ)), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1)));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            assume ORD#IsNat(Lit(ORD#FromNat(1)));
            assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume _module.Stream.Cons_q(s#1);
            ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#0, TORDINAL, $Heap);
            ##s#2 := _module.Stream.tail(s#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#2, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1));
            assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1));
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            assume _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1));
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assert _module.Stream.Cons_q(s#1);
            assume _module.Tree.Node_q($Unbox(_module.Stream.head(s#1)): DatatypeType);
            ##_k#1 := ORD#Minus(_k#0, ORD#FromNat(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##_k#1, TORDINAL, $Heap);
            ##s#3 := _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#3, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType));
            if (!_module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), 
              ORD#Minus(_k#0, ORD#FromNat(1)), 
              _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType)))
            {
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assert _module.Stream.Cons_q(s#1);
                ##_k#2 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#2, TORDINAL, $Heap);
                ##s#4 := _module.Stream.tail(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#4, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                assume _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1));
            }

            assume _module.Tree.Node_q($Unbox(_module.Stream.head(s#1)): DatatypeType)
               && _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType))
               && (!_module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType))
                 ==> _module.__default.InfiniteHeightSomewhere__Bad_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1)));
            // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(195,3)
            assert {:subsumption 0} _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1))
               ==> _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LS($LZ)), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Tree.children($Unbox(_module.Stream.head(s#1)): DatatypeType))
                 || _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LS($LZ)), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1));
            assume false;
        }

        assume _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#1))
           ==> _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), _k#0, s#1);
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(191,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, s#2: DatatypeType :: 
          $Is(s#2, Tclass._module.Stream(Tclass._module.Tree()))
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.IsNeverEndingStream(Tclass._module.Tree(), $LS($LZ), s#2)
             ==> _module.__default.InfiniteHeightSomewhere__Bad_h($LS($LZ), _k'#0, s#2));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(191,15)"} true;
    }
}



// function declaration for _module._default.ValidPath
function _module.__default.ValidPath($ly: LayerType, t#0: DatatypeType, p#0: DatatypeType) : bool;

function _module.__default.ValidPath#canCall(t#0: DatatypeType, p#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.ValidPath($LS($ly), t#0, p#0) } 
  _module.__default.ValidPath($LS($ly), t#0, p#0)
     == _module.__default.ValidPath($ly, t#0, p#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.ValidPath(AsFuelBottom($ly), t#0, p#0) } 
  _module.__default.ValidPath($ly, t#0, p#0)
     == _module.__default.ValidPath($LZ, t#0, p#0));

// consequence axiom for _module.__default.ValidPath
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, p#0: DatatypeType :: 
    { _module.__default.ValidPath($ly, t#0, p#0) } 
    _module.__default.ValidPath#canCall(t#0, p#0)
         || (20 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(p#0, Tclass._module.Stream(TInt)))
       ==> true);

function _module.__default.ValidPath#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ValidPath
axiom (forall $ly: LayerType, t#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.ValidPath#requires($ly, t#0, p#0) } 
  $Is(t#0, Tclass._module.Tree()) && $Is(p#0, Tclass._module.Stream(TInt))
     ==> _module.__default.ValidPath#requires($ly, t#0, p#0) == true);

// definition axiom for _module.__default.ValidPath (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, p#0: DatatypeType :: 
    { _module.__default.ValidPath($LS($ly), t#0, p#0) } 
    _module.__default.ValidPath#canCall(t#0, p#0)
         || (20 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(p#0, Tclass._module.Stream(TInt)))
       ==> (_module.Stream.Nil_q(p#0) ==> $IsA#_module.Tree(t#0))
         && (!_module.Stream.Nil_q(p#0)
           ==> (var tail#1 := _module.Stream.tail(p#0); 
            (var index#1 := $Unbox(_module.Stream.head(p#0)): int; 
              LitInt(0) <= index#1
                 ==> _module.Tree.Node_q(t#0)
                   && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#1)
                   && (var ch#1 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#1); 
                    _module.Stream.Cons_q(ch#1)
                       ==> _module.__default.ValidPath#canCall($Unbox(_module.Stream.head(ch#1)): DatatypeType, tail#1)))))
         && _module.__default.ValidPath($LS($ly), t#0, p#0)
           == (if _module.Stream.Nil_q(p#0)
             then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
             else (var tail#0 := _module.Stream.tail(p#0); 
              (var index#0 := $Unbox(_module.Stream.head(p#0)): int; 
                LitInt(0) <= index#0
                   && (var ch#0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#0); 
                    _module.Stream.Cons_q(ch#0)
                       && _module.__default.ValidPath($ly, $Unbox(_module.Stream.head(ch#0)): DatatypeType, tail#0))))));

// 1st prefix predicate axiom for _module.__default.ValidPath_h
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, p#0: DatatypeType :: 
    { _module.__default.ValidPath($LS($ly), t#0, p#0) } 
    $Is(t#0, Tclass._module.Tree())
         && $Is(p#0, Tclass._module.Stream(TInt))
         && _module.__default.ValidPath($LS($ly), t#0, p#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.ValidPath_h($LS($ly), _k#0, t#0, p#0) } 
        _module.__default.ValidPath_h($LS($ly), _k#0, t#0, p#0)));

// 2nd prefix predicate axiom
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, p#0: DatatypeType :: 
    { _module.__default.ValidPath($LS($ly), t#0, p#0) } 
    $Is(t#0, Tclass._module.Tree())
         && $Is(p#0, Tclass._module.Stream(TInt))
         && (forall _k#0: Box :: 
          { _module.__default.ValidPath_h($LS($ly), _k#0, t#0, p#0) } 
          _module.__default.ValidPath_h($LS($ly), _k#0, t#0, p#0))
       ==> _module.__default.ValidPath($LS($ly), t#0, p#0));

// 3rd prefix predicate axiom
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, p#0: DatatypeType, _k#0: Box :: 
    { _module.__default.ValidPath_h($ly, _k#0, t#0, p#0) } 
    $Is(t#0, Tclass._module.Tree())
         && $Is(p#0, Tclass._module.Stream(TInt))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.ValidPath_h($ly, _k#0, t#0, p#0));

procedure CheckWellformed$$_module.__default.ValidPath(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()), 
    p#0: DatatypeType where $Is(p#0, Tclass._module.Stream(TInt)));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ValidPath(t#0: DatatypeType, p#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var index#Z#0: int;
  var let#1#0#0: int;
  var ch#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var ##t#0: DatatypeType;
  var ##p#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ValidPath
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(234,19): initial state"} true;
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
        if (p#0 == #_module.Stream.Nil())
        {
            assume _module.__default.ValidPath($LS($LZ), t#0, p#0)
               == _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())));
            assume $IsA#_module.Tree(t#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ValidPath($LS($LZ), t#0, p#0), TBool);
        }
        else if (p#0 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.Stream(TInt));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.Stream(TInt));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(TInt));
            assume tail#Z#0 == let#0#0#0;
            havoc index#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume index#Z#0 == let#1#0#0;
            if (LitInt(0) <= index#Z#0)
            {
                havoc ch#Z#0;
                assume $Is(ch#Z#0, Tclass._module.Stream(Tclass._module.Tree()));
                assume _module.Tree.Node_q(t#0);
                ##s#0 := _module.Tree.children(t#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                assert $Is(index#Z#0, Tclass._System.nat());
                ##n#0 := index#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#Z#0);
                assume let#2#0#0
                   == _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#Z#0);
                assume _module.Tree.Node_q(t#0)
                   && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(let#2#0#0, Tclass._module.Stream(Tclass._module.Tree()));
                assume ch#Z#0 == let#2#0#0;
                if (_module.Stream.Cons_q(ch#Z#0))
                {
                    assert _module.Stream.Cons_q(ch#Z#0);
                    ##t#0 := $Unbox(_module.Stream.head(ch#Z#0)): DatatypeType;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
                    ##p#0 := tail#Z#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##p#0, Tclass._module.Stream(TInt), $Heap);
                    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    assume _module.__default.ValidPath#canCall($Unbox(_module.Stream.head(ch#Z#0)): DatatypeType, tail#Z#0);
                }
            }

            assume _module.__default.ValidPath($LS($LZ), t#0, p#0)
               == (LitInt(0) <= index#Z#0
                 && (var ch#2 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#Z#0); 
                  _module.Stream.Cons_q(ch#2)
                     && _module.__default.ValidPath($LS($LZ), $Unbox(_module.Stream.head(ch#2)): DatatypeType, tail#Z#0)));
            assume LitInt(0) <= index#Z#0
               ==> _module.Tree.Node_q(t#0)
                 && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#Z#0)
                 && (var ch#2 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#Z#0); 
                  _module.Stream.Cons_q(ch#2)
                     ==> _module.__default.ValidPath#canCall($Unbox(_module.Stream.head(ch#2)): DatatypeType, tail#Z#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ValidPath($LS($LZ), t#0, p#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.ValidPath#
function _module.__default.ValidPath_h($ly: LayerType, _k#0: Box, t#0: DatatypeType, p#0: DatatypeType) : bool;

function _module.__default.ValidPath_h#canCall(_k#0: Box, t#0: DatatypeType, p#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.ValidPath_h($LS($ly), _k#0, t#0, p#0) } 
  _module.__default.ValidPath_h($LS($ly), _k#0, t#0, p#0)
     == _module.__default.ValidPath_h($ly, _k#0, t#0, p#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.ValidPath_h(AsFuelBottom($ly), _k#0, t#0, p#0) } 
  _module.__default.ValidPath_h($ly, _k#0, t#0, p#0)
     == _module.__default.ValidPath_h($LZ, _k#0, t#0, p#0));

// consequence axiom for _module.__default.ValidPath_h
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, p#0: DatatypeType :: 
    { _module.__default.ValidPath_h($ly, _k#0, t#0, p#0) } 
    _module.__default.ValidPath_h#canCall(_k#0, t#0, p#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(p#0, Tclass._module.Stream(TInt)))
       ==> true);

function _module.__default.ValidPath_h#requires(LayerType, Box, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ValidPath_h
axiom (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, p#0: DatatypeType :: 
  { _module.__default.ValidPath_h#requires($ly, _k#0, t#0, p#0) } 
  $Is(t#0, Tclass._module.Tree()) && $Is(p#0, Tclass._module.Stream(TInt))
     ==> _module.__default.ValidPath_h#requires($ly, _k#0, t#0, p#0) == true);

// definition axiom for _module.__default.ValidPath_h (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, p#0: DatatypeType :: 
    { _module.__default.ValidPath_h($LS($ly), _k#0, t#0, p#0) } 
    _module.__default.ValidPath_h#canCall(_k#0, t#0, p#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(p#0, Tclass._module.Stream(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Stream.Nil_q(p#0) ==> $IsA#_module.Tree(t#0))
             && (!_module.Stream.Nil_q(p#0)
               ==> (var tail#3 := _module.Stream.tail(p#0); 
                (var index#3 := $Unbox(_module.Stream.head(p#0)): int; 
                  LitInt(0) <= index#3
                     ==> _module.Tree.Node_q(t#0)
                       && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#3)
                       && (var ch#4 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#3); 
                        _module.Stream.Cons_q(ch#4)
                           ==> _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $Unbox(_module.Stream.head(ch#4)): DatatypeType, 
                            tail#3))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(p#0)
             then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
             else (var tail#4 := _module.Stream.tail(p#0); 
              (var index#4 := $Unbox(_module.Stream.head(p#0)): int; 
                LitInt(0) <= index#4
                   && (var ch#5 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#4); 
                    _module.Stream.Cons_q(ch#5)
                       && _module.__default.ValidPath_h($ly, 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        $Unbox(_module.Stream.head(ch#5)): DatatypeType, 
                        tail#4))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.ValidPath_h($ly, _k'#0, t#0, p#0) } 
            ORD#Less(_k'#0, _k#0) ==> _module.__default.ValidPath_h#canCall(_k'#0, t#0, p#0)))
         && _module.__default.ValidPath_h($LS($ly), _k#0, t#0, p#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(p#0)
                 then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
                 else (var tail#2 := _module.Stream.tail(p#0); 
                  (var index#2 := $Unbox(_module.Stream.head(p#0)): int; 
                    LitInt(0) <= index#2
                       && (var ch#3 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#2); 
                        _module.Stream.Cons_q(ch#3)
                           && _module.__default.ValidPath_h($ly, 
                            ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $Unbox(_module.Stream.head(ch#3)): DatatypeType, 
                            tail#2))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.ValidPath_h($ly, _k'#0, t#0, p#0) } 
                ORD#Less(_k'#0, _k#0) ==> _module.__default.ValidPath_h($ly, _k'#0, t#0, p#0)))));

// definition axiom for _module.__default.ValidPath_h for decreasing-related literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, p#0: DatatypeType :: 
    {:weight 3} { _module.__default.ValidPath_h($LS($ly), Lit(_k#0), t#0, p#0) } 
    _module.__default.ValidPath_h#canCall(Lit(_k#0), t#0, p#0)
         || (21 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(p#0, Tclass._module.Stream(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Stream.Nil_q(p#0) ==> $IsA#_module.Tree(t#0))
             && (!_module.Stream.Nil_q(p#0)
               ==> (var tail#6 := _module.Stream.tail(p#0); 
                (var index#6 := $Unbox(_module.Stream.head(p#0)): int; 
                  LitInt(0) <= index#6
                     ==> _module.Tree.Node_q(t#0)
                       && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#6)
                       && (var ch#7 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#6); 
                        _module.Stream.Cons_q(ch#7)
                           ==> _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $Unbox(_module.Stream.head(ch#7)): DatatypeType, 
                            tail#6))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(p#0)
             then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
             else (var tail#7 := _module.Stream.tail(p#0); 
              (var index#7 := $Unbox(_module.Stream.head(p#0)): int; 
                LitInt(0) <= index#7
                   && (var ch#8 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#7); 
                    _module.Stream.Cons_q(ch#8)
                       && _module.__default.ValidPath_h($LS($ly), 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        $Unbox(_module.Stream.head(ch#8)): DatatypeType, 
                        tail#7))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.ValidPath_h($LS($ly), _k'#1, t#0, p#0) } 
            ORD#Less(_k'#1, _k#0) ==> _module.__default.ValidPath_h#canCall(_k'#1, t#0, p#0)))
         && _module.__default.ValidPath_h($LS($ly), Lit(_k#0), t#0, p#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(p#0)
                 then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
                 else (var tail#5 := _module.Stream.tail(p#0); 
                  (var index#5 := $Unbox(_module.Stream.head(p#0)): int; 
                    LitInt(0) <= index#5
                       && (var ch#6 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#5); 
                        _module.Stream.Cons_q(ch#6)
                           && _module.__default.ValidPath_h($LS($ly), 
                            ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $Unbox(_module.Stream.head(ch#6)): DatatypeType, 
                            tail#5))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.ValidPath_h($LS($ly), _k'#1, t#0, p#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.ValidPath_h($LS($ly), _k'#1, t#0, p#0)))));

// definition axiom for _module.__default.ValidPath_h for all literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, p#0: DatatypeType :: 
    {:weight 3} { _module.__default.ValidPath_h($LS($ly), Lit(_k#0), Lit(t#0), Lit(p#0)) } 
    _module.__default.ValidPath_h#canCall(Lit(_k#0), Lit(t#0), Lit(p#0))
         || (21 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(p#0, Tclass._module.Stream(TInt)))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Stream.Nil_q(p#0) ==> $IsA#_module.Tree(t#0))
             && (!_module.Stream.Nil_q(p#0)
               ==> (var tail#9 := _module.Stream.tail(p#0); 
                (var index#9 := $Unbox(_module.Stream.head(p#0)): int; 
                  LitInt(0) <= index#9
                     ==> _module.Tree.Node_q(t#0)
                       && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#9)
                       && (var ch#10 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#9); 
                        _module.Stream.Cons_q(ch#10)
                           ==> _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $Unbox(_module.Stream.head(ch#10)): DatatypeType, 
                            tail#9))))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Stream.Nil_q(p#0)
             then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
             else (var tail#10 := _module.Stream.tail(p#0); 
              (var index#10 := $Unbox(_module.Stream.head(p#0)): int; 
                LitInt(0) <= index#10
                   && (var ch#11 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#10); 
                    _module.Stream.Cons_q(ch#11)
                       && _module.__default.ValidPath_h($LS($ly), 
                        ORD#Minus(_k#0, ORD#FromNat(1)), 
                        $Unbox(_module.Stream.head(ch#11)): DatatypeType, 
                        tail#10))))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.ValidPath_h($LS($ly), _k'#2, t#0, p#0) } 
            ORD#Less(_k'#2, _k#0) ==> _module.__default.ValidPath_h#canCall(_k'#2, t#0, p#0)))
         && _module.__default.ValidPath_h($LS($ly), Lit(_k#0), Lit(t#0), Lit(p#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Stream.Nil_q(p#0)
                 then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
                 else (var tail#8 := _module.Stream.tail(p#0); 
                  (var index#8 := $Unbox(_module.Stream.head(p#0)): int; 
                    LitInt(0) <= index#8
                       && (var ch#9 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#8); 
                        _module.Stream.Cons_q(ch#9)
                           && _module.__default.ValidPath_h($LS($ly), 
                            ORD#Minus(_k#0, ORD#FromNat(1)), 
                            $Unbox(_module.Stream.head(ch#9)): DatatypeType, 
                            tail#8))))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.ValidPath_h($LS($ly), _k'#2, t#0, p#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.ValidPath_h($LS($ly), _k'#2, t#0, p#0)))));

procedure {:_induction p#0} CheckWellformed$$_module.__default.ValidPath__Lemma(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction p#0} Call$$_module.__default.ValidPath__Lemma(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValidPath#canCall(Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0)
     && (_module.__default.ValidPath($LS($LZ), Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0)
       ==> $IsA#_module.Stream(p#0));
  ensures _module.__default.ValidPath($LS($LZ), Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0)
     ==> $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), p#0, #_module.Stream.Nil());
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction p#0} Impl$$_module.__default.ValidPath__Lemma(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0))
   returns ($_reverifyPost: bool);
  free requires 51 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ValidPath#canCall(Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0)
     && (_module.__default.ValidPath($LS($LZ), Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0)
       ==> $IsA#_module.Stream(p#0));
  ensures _module.__default.ValidPath($LS($LZ), Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0)
     ==> $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), p#0, #_module.Stream.Nil());
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction p#0} Impl$$_module.__default.ValidPath__Lemma(p#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##t#1: DatatypeType;
  var ##p#1: DatatypeType;
  var _mcc#0#0_0_0: int;
  var _mcc#1#0_0_0: DatatypeType;
  var tail#0_0_0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var index#0_0_0: int;
  var let#0_0_1#0#0: int;
  var nil#0_0_0: DatatypeType
     where $Is(nil#0_0_0, Tclass._module.Stream(Tclass._module.Tree()))
       && $IsAlloc(nil#0_0_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
  var s##0_0_0: DatatypeType;
  var k##0_0_0: int;
  var n##0_0_0: int;

    // AddMethodImpl: ValidPath_Lemma, Impl$$_module.__default.ValidPath__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(245,0): initial state"} true;
    assume $IsA#_module.Stream(p#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#p0#0: DatatypeType :: 
      $Is($ih#p0#0, Tclass._module.Stream(TInt)) && Lit(true) && false
         ==> 
        _module.__default.ValidPath($LS($LZ), Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), $ih#p0#0)
         ==> $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), $ih#p0#0, #_module.Stream.Nil()));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(246,3)
    ##t#1 := Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil())));
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#1, Tclass._module.Tree(), $Heap);
    ##p#1 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#1, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.ValidPath#canCall(Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0);
    assume _module.__default.ValidPath#canCall(Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0);
    if (_module.__default.ValidPath($LS($LZ), Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil()))), p#0))
    {
        assume true;
        havoc _mcc#0#0_0_0, _mcc#1#0_0_0;
        if (p#0 == #_module.Stream.Nil())
        {
        }
        else if (p#0 == #_module.Stream.Cons($Box(_mcc#0#0_0_0), _mcc#1#0_0_0))
        {
            assume $Is(_mcc#1#0_0_0, Tclass._module.Stream(TInt));
            havoc tail#0_0_0;
            assume $Is(tail#0_0_0, Tclass._module.Stream(TInt))
               && $IsAlloc(tail#0_0_0, Tclass._module.Stream(TInt), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0_0_0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(TInt));
            assume tail#0_0_0 == let#0_0_0#0#0;
            havoc index#0_0_0;
            assume let#0_0_1#0#0 == _mcc#0#0_0_0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_1#0#0, TInt);
            assume index#0_0_0 == let#0_0_1#0#0;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(250,32)
            assume true;
            assume true;
            nil#0_0_0 := Lit(#_module.Stream.Nil());
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(250,37)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(251,20)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##0_0_0 := nil#0_0_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(LitInt(0), Tclass._System.nat());
            k##0_0_0 := LitInt(0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(index#0_0_0, Tclass._System.nat());
            n##0_0_0 := index#0_0_0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Tail__Lemma1(Tclass._module.Tree(), s##0_0_0, k##0_0_0, n##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(251,34)"} true;
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



// function declaration for _module._default.HasFiniteHeight
function _module.__default.HasFiniteHeight(t#0: DatatypeType) : bool;

function _module.__default.HasFiniteHeight#canCall(t#0: DatatypeType) : bool;

// consequence axiom for _module.__default.HasFiniteHeight
axiom 52 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.HasFiniteHeight(t#0) } 
    _module.__default.HasFiniteHeight#canCall(t#0)
         || (52 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> true);

function _module.__default.HasFiniteHeight#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.HasFiniteHeight
axiom (forall t#0: DatatypeType :: 
  { _module.__default.HasFiniteHeight#requires(t#0) } 
  $Is(t#0, Tclass._module.Tree())
     ==> _module.__default.HasFiniteHeight#requires(t#0) == true);

// definition axiom for _module.__default.HasFiniteHeight (revealed)
axiom 52 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.HasFiniteHeight(t#0) } 
    _module.__default.HasFiniteHeight#canCall(t#0)
         || (52 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (forall p#0: DatatypeType :: 
          { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0) } 
            { _module.__default.ValidPath($LS($LZ), t#0, p#0) } 
          $Is(p#0, Tclass._module.Stream(TInt))
             ==> _module.__default.ValidPath#canCall(t#0, p#0)
               && (_module.__default.ValidPath($LS($LZ), t#0, p#0)
                 ==> _module.__default.IsNeverEndingStream#canCall(TInt, p#0)))
         && _module.__default.HasFiniteHeight(t#0)
           == (forall p#0: DatatypeType :: 
            { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0) } 
              { _module.__default.ValidPath($LS($LZ), t#0, p#0) } 
            $Is(p#0, Tclass._module.Stream(TInt))
               ==> 
              _module.__default.ValidPath($LS($LZ), t#0, p#0)
               ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0)));

// definition axiom for _module.__default.HasFiniteHeight for all literals (revealed)
axiom 52 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    {:weight 3} { _module.__default.HasFiniteHeight(Lit(t#0)) } 
    _module.__default.HasFiniteHeight#canCall(Lit(t#0))
         || (52 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (forall p#1: DatatypeType :: 
          { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#1) } 
            { _module.__default.ValidPath($LS($LZ), t#0, p#1) } 
          $Is(p#1, Tclass._module.Stream(TInt))
             ==> _module.__default.ValidPath#canCall(Lit(t#0), p#1)
               && (_module.__default.ValidPath($LS($LZ), Lit(t#0), p#1)
                 ==> _module.__default.IsNeverEndingStream#canCall(TInt, p#1)))
         && _module.__default.HasFiniteHeight(Lit(t#0))
           == (forall p#1: DatatypeType :: 
            { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#1) } 
              { _module.__default.ValidPath($LS($LZ), t#0, p#1) } 
            $Is(p#1, Tclass._module.Stream(TInt))
               ==> 
              _module.__default.ValidPath($LS($LZ), Lit(t#0), p#1)
               ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#1)));

procedure CheckWellformed$$_module.__default.HasFiniteHeight(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()));
  free requires 52 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.HasFiniteHeight(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var p#2: DatatypeType;
  var ##t#0: DatatypeType;
  var ##p#0: DatatypeType;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function HasFiniteHeight
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(258,10): initial state"} true;
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
        // Begin Comprehension WF check
        havoc p#2;
        if ($Is(p#2, Tclass._module.Stream(TInt)))
        {
            ##t#0 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
            ##p#0 := p#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#0, Tclass._module.Stream(TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.ValidPath#canCall(t#0, p#2);
            if (_module.__default.ValidPath($LS($LZ), t#0, p#2))
            {
                ##s#0 := p#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.IsNeverEndingStream#canCall(TInt, p#2);
            }
        }

        // End Comprehension WF check
        assume _module.__default.HasFiniteHeight(t#0)
           == (forall p#3: DatatypeType :: 
            { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#3) } 
              { _module.__default.ValidPath($LS($LZ), t#0, p#3) } 
            $Is(p#3, Tclass._module.Stream(TInt))
               ==> 
              _module.__default.ValidPath($LS($LZ), t#0, p#3)
               ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#3));
        assume (forall p#3: DatatypeType :: 
          { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#3) } 
            { _module.__default.ValidPath($LS($LZ), t#0, p#3) } 
          $Is(p#3, Tclass._module.Stream(TInt))
             ==> _module.__default.ValidPath#canCall(t#0, p#3)
               && (_module.__default.ValidPath($LS($LZ), t#0, p#3)
                 ==> _module.__default.IsNeverEndingStream#canCall(TInt, p#3)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.HasFiniteHeight(t#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.Theorem1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0));
  free requires 54 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0));
  // user-defined preconditions
  requires _module.__default.HasBoundedHeight#canCall(t#0)
     ==> _module.__default.HasBoundedHeight(t#0)
       || (exists n#0: int :: 
        { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0) } 
        LitInt(0) <= n#0
           && 
          LitInt(0) <= n#0
           && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.HasFiniteHeight#canCall(t#0);
  free ensures _module.__default.HasFiniteHeight#canCall(t#0)
     && 
    _module.__default.HasFiniteHeight(t#0)
     && (forall p#0: DatatypeType :: 
      { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0) } 
        { _module.__default.ValidPath($LS($LZ), t#0, p#0) } 
      $Is(p#0, Tclass._module.Stream(TInt))
         ==> 
        _module.__default.ValidPath($LS($LZ), t#0, p#0)
         ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Theorem1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0))
   returns ($_reverifyPost: bool);
  free requires 54 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.HasBoundedHeight#canCall(t#0)
     && 
    _module.__default.HasBoundedHeight(t#0)
     && (exists n#1: int :: 
      { _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#1) } 
      LitInt(0) <= n#1
         && 
        LitInt(0) <= n#1
         && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.HasFiniteHeight#canCall(t#0);
  ensures _module.__default.HasFiniteHeight#canCall(t#0)
     ==> _module.__default.HasFiniteHeight(t#0)
       || (forall p#1: DatatypeType :: 
        { _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1) } 
          { _module.__default.ValidPath($LS($LS($LZ)), t#0, p#1) } 
        $Is(p#1, Tclass._module.Stream(TInt))
           ==> 
          _module.__default.ValidPath($LS($LS($LZ)), t#0, p#1)
           ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Theorem1(t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#2: int where LitInt(0) <= n#2;
  var n#3: int;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var p#2: DatatypeType;
  var ##t#2: DatatypeType;
  var ##p#0: DatatypeType;
  var t##0: DatatypeType;
  var n##0: int;
  var p##0: DatatypeType;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Theorem1, Impl$$_module.__default.Theorem1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(268,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(269,9)
    havoc n#3;
    if (LitInt(0) <= n#3)
    {
        if (LitInt(0) <= n#3)
        {
            assume _module.Tree.Node_q(t#0);
            ##s#0 := _module.Tree.children(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#0 := n#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#3);
        }

        assume LitInt(0) <= n#3
           ==> _module.Tree.Node_q(t#0)
             && _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#3);
    }

    assert ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), LitInt(0)))
       || 
      ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), LitInt(0)))
       || 
      ($Is(LitInt(0), Tclass._System.nat())
         && 
        LitInt(0) <= LitInt(0)
         && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), LitInt(0)))
       || (exists $as#n0#0: int :: 
        LitInt(0) <= $as#n0#0
           && 
          LitInt(0) <= $as#n0#0
           && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), $as#n0#0));
    havoc n#2;
    assume LitInt(0) <= n#2
       && _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#2);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(269,45)"} true;
    // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(270,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc p#2;
        assume $Is(p#2, Tclass._module.Stream(TInt));
        ##t#2 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
        ##p#0 := p#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#0, Tclass._module.Stream(TInt), $Heap);
        assume _module.__default.ValidPath#canCall(t#0, p#2);
        assume _module.__default.ValidPath#canCall(t#0, p#2);
        assume _module.__default.ValidPath($LS($LZ), t#0, p#2);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(271,19)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0 := t#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0 := n#2;
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0 := p#2;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Theorem1__Lemma(t##0, n##0, p##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(271,27)"} true;
        assume false;
    }
    else
    {
        $initHeapForallStmt#0 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#0 == $Heap;
        assume (forall p#3: DatatypeType :: 
          { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#3) } 
            { _module.__default.ValidPath($LS($LZ), t#0, p#3) } 
          $Is(p#3, Tclass._module.Stream(TInt))
               && _module.__default.ValidPath($LS($LZ), t#0, p#3)
             ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#3));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(272,2)"} true;
}



procedure {:_induction t#0, n#0, p#0} CheckWellformed$$_module.__default.Theorem1__Lemma(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    n#0: int where LitInt(0) <= n#0, 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  free requires 53 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction t#0, n#0, p#0} Call$$_module.__default.Theorem1__Lemma(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    n#0: int where LitInt(0) <= n#0, 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  // user-defined preconditions
  requires _module.__default.LowerThan($LS($LS($LZ)), _module.Tree.children(t#0), n#0);
  requires _module.__default.ValidPath($LS($LS($LZ)), t#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
  ensures !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction t#0, n#0, p#0} Impl$$_module.__default.Theorem1__Lemma(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    n#0: int where LitInt(0) <= n#0, 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0))
   returns ($_reverifyPost: bool);
  free requires 53 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.LowerThan($LS($LS($LZ)), _module.Tree.children(t#0), n#0);
  requires _module.__default.ValidPath($LS($LS($LZ)), t#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
  ensures !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction t#0, n#0, p#0} Impl$$_module.__default.Theorem1__Lemma(t#0: DatatypeType, n#0: int, p#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: int;
  var _mcc#1#0_0: DatatypeType;
  var tail#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var index#0_0: int;
  var let#0_1#0#0: int;
  var ch#0_0: DatatypeType
     where $Is(ch#0_0, Tclass._module.Stream(Tclass._module.Tree()))
       && $IsAlloc(ch#0_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
  var ##s#0_0: DatatypeType;
  var ##n#0_0: int;
  var ##s#0_0_0_0: DatatypeType;
  var ##s#0_0_0_1: DatatypeType;
  var ##s#0_0_1_0: DatatypeType;
  var ##n#0_0_1_0: int;
  var ##s#0_0_1_1: DatatypeType;
  var ##s#0_0_2_0: DatatypeType;
  var ##n#0_0_2_0: int;
  var ##s#0_0_2_1: DatatypeType;
  var ##n#0_0_2_1: int;
  var ##s#0_0_3_0: DatatypeType;
  var ##n#0_0_3_0: int;
  var s##0_0_3_0: DatatypeType;
  var n##0_0_3_0: int;
  var h##0_0_3_0: int;
  var ##s#0_0_3_1: DatatypeType;
  var ##n#0_0_3_1: int;
  var ##s#0_0_0: DatatypeType;
  var ##n#0_0_0: int;

    // AddMethodImpl: Theorem1_Lemma, Impl$$_module.__default.Theorem1__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(278,0): initial state"} true;
    assume $IsA#_module.Tree(t#0);
    assume $IsA#_module.Stream(p#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#t0#0: DatatypeType, $ih#n0#0: int, $ih#p0#0: DatatypeType :: 
      $Is($ih#t0#0, Tclass._module.Tree())
           && LitInt(0) <= $ih#n0#0
           && $Is($ih#p0#0, Tclass._module.Stream(TInt))
           && 
          _module.__default.LowerThan($LS($LZ), _module.Tree.children($ih#t0#0), $ih#n0#0)
           && _module.__default.ValidPath($LS($LZ), $ih#t0#0, $ih#p0#0)
           && 
          0 <= $ih#n0#0
           && $ih#n0#0 < n#0
         ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), $ih#p0#0));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (p#0 == #_module.Stream.Nil())
    {
    }
    else if (p#0 == #_module.Stream.Cons($Box(_mcc#0#0_0), _mcc#1#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass._module.Stream(TInt));
        havoc tail#0_0;
        assume $Is(tail#0_0, Tclass._module.Stream(TInt))
           && $IsAlloc(tail#0_0, Tclass._module.Stream(TInt), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Stream(TInt));
        assume tail#0_0 == let#0_0#0#0;
        havoc index#0_0;
        assume let#0_1#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TInt);
        assume index#0_0 == let#0_1#0#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(282,14)
        assume true;
        assume _module.Tree.Node_q(t#0);
        ##s#0_0 := _module.Tree.children(t#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        assert $Is(index#0_0, Tclass._System.nat());
        ##n#0_0 := index#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#0_0);
        assume _module.Tree.Node_q(t#0)
           && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#0_0);
        ch#0_0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(282,39)"} true;
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assume _module.Tree.Node_q(t#0);
            ##s#0_0_0 := _module.Tree.children(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#0_0_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_0, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#0);
            assume _module.Tree.Node_q(t#0)
               && _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assume _module.Tree.Node_q(t#0);
            ##s#0_0_3_0 := _module.Tree.children(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_3_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#0_0_3_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_0, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#0);
            assume _module.Tree.Node_q(t#0)
               && _module.__default.LowerThan#canCall(_module.Tree.children(t#0), n#0);
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assume _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0);
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(285,29)
            // TrCallStmt: Before ProcessCallStmt
            assume _module.Tree.Node_q(t#0);
            assume _module.Tree.Node_q(t#0);
            // ProcessCallStmt: CheckSubrange
            s##0_0_3_0 := _module.Tree.children(t#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(index#0_0, Tclass._System.nat());
            n##0_0_3_0 := index#0_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            h##0_0_3_0 := n#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.LowerThan__Lemma(s##0_0_3_0, n##0_0_3_0, h##0_0_3_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(285,50)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            ##s#0_0_3_1 := ch#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_3_1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#0_0_3_1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_3_1, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(ch#0_0, n#0);
            assume _module.__default.LowerThan#canCall(ch#0_0, n#0);
            // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assert {:subsumption 0} _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0)
               ==> _module.__default.LowerThan($LS($LS($LZ)), ch#0_0, n#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            ##s#0_0_2_0 := ch#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_2_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#0_0_2_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_2_0, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(ch#0_0, n#0);
            assume _module.__default.LowerThan#canCall(ch#0_0, n#0);
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assume _module.__default.LowerThan($LS($LZ), ch#0_0, n#0);
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assert _module.Stream.Cons_q(ch#0_0);
            assume _module.Tree.Node_q($Unbox(_module.Stream.head(ch#0_0)): DatatypeType);
            ##s#0_0_2_1 := _module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_2_1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0_0_2_1 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_2_1, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(_module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
              n#0 - 1);
            assume _module.Tree.Node_q($Unbox(_module.Stream.head(ch#0_0)): DatatypeType)
               && _module.__default.LowerThan#canCall(_module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
                n#0 - 1);
            // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assert {:subsumption 0} _module.__default.LowerThan($LS($LZ), ch#0_0, n#0)
               ==> _module.__default.LowerThan($LS($LS($LZ)), 
                _module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
                n#0 - 1);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assume _module.Stream.Cons_q(ch#0_0);
            assume _module.Tree.Node_q($Unbox(_module.Stream.head(ch#0_0)): DatatypeType);
            ##s#0_0_1_0 := _module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_1_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume $Is(n#0 - 1, Tclass._System.nat());
            ##n#0_0_1_0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0_0_1_0, Tclass._System.nat(), $Heap);
            assume _module.__default.LowerThan#canCall(_module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
              n#0 - 1);
            assume _module.Tree.Node_q($Unbox(_module.Stream.head(ch#0_0)): DatatypeType)
               && _module.__default.LowerThan#canCall(_module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
                n#0 - 1);
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assume _module.__default.LowerThan($LS($LZ), 
              _module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
              n#0 - 1);
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            ##s#0_0_1_1 := tail#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_1_1, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.IsNeverEndingStream#canCall(TInt, tail#0_0);
            assume _module.__default.IsNeverEndingStream#canCall(TInt, tail#0_0);
            // ----- assert line2 ==> line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assert {:subsumption 0} _module.__default.LowerThan($LS($LZ), 
                _module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
                n#0 - 1)
               ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), tail#0_0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            ##s#0_0_0_0 := tail#0_0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_0_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.IsNeverEndingStream#canCall(TInt, tail#0_0);
            assume _module.__default.IsNeverEndingStream#canCall(TInt, tail#0_0);
            // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assume !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), tail#0_0);
            // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            ##s#0_0_0_1 := p#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0_0_0_1, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
            assume _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
            // ----- assert line3 ==> line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(283,7)
            assert {:subsumption 0} !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), tail#0_0)
               ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0);
            assume false;
        }

        assume _module.__default.LowerThan($LS($LZ), _module.Tree.children(t#0), n#0)
           ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0);
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.SkinnyFiniteTree
function _module.__default.SkinnyFiniteTree($ly: LayerType, n#0: int) : DatatypeType;

function _module.__default.SkinnyFiniteTree#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.SkinnyFiniteTree($LS($ly), n#0) } 
  _module.__default.SkinnyFiniteTree($LS($ly), n#0)
     == _module.__default.SkinnyFiniteTree($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.SkinnyFiniteTree(AsFuelBottom($ly), n#0) } 
  _module.__default.SkinnyFiniteTree($ly, n#0)
     == _module.__default.SkinnyFiniteTree($LZ, n#0));

// consequence axiom for _module.__default.SkinnyFiniteTree
axiom 55 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.SkinnyFiniteTree($ly, n#0) } 
    _module.__default.SkinnyFiniteTree#canCall(n#0)
         || (55 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (forall k#0: int :: 
          { _module.__default.LowerThan($LS($LZ), 
              _module.Tree.children(_module.__default.SkinnyFiniteTree($ly, n#0)), 
              k#0) } 
          LitInt(0) <= k#0
             ==> (_module.__default.LowerThan($LS($LZ), 
                _module.Tree.children(_module.__default.SkinnyFiniteTree($ly, n#0)), 
                k#0)
               <==> n#0 <= k#0))
         && $Is(_module.__default.SkinnyFiniteTree($ly, n#0), Tclass._module.Tree()));

function _module.__default.SkinnyFiniteTree#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.SkinnyFiniteTree
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.SkinnyFiniteTree#requires($ly, n#0) } 
  LitInt(0) <= n#0
     ==> _module.__default.SkinnyFiniteTree#requires($ly, n#0) == true);

// definition axiom for _module.__default.SkinnyFiniteTree (revealed)
axiom 55 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.SkinnyFiniteTree($LS($ly), n#0) } 
    _module.__default.SkinnyFiniteTree#canCall(n#0)
         || (55 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> _module.__default.SkinnyFiniteTree#canCall(n#0 - 1))
         && _module.__default.SkinnyFiniteTree($LS($ly), n#0)
           == (if n#0 == LitInt(0)
             then #_module.Tree.Node(Lit(#_module.Stream.Nil()))
             else #_module.Tree.Node(#_module.Stream.Cons($Box(_module.__default.SkinnyFiniteTree($ly, n#0 - 1)), 
                Lit(#_module.Stream.Nil())))));

// definition axiom for _module.__default.SkinnyFiniteTree for all literals (revealed)
axiom 55 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.SkinnyFiniteTree($LS($ly), LitInt(n#0)) } 
    _module.__default.SkinnyFiniteTree#canCall(LitInt(n#0))
         || (55 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.__default.SkinnyFiniteTree#canCall(LitInt(n#0 - 1)))
         && _module.__default.SkinnyFiniteTree($LS($ly), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then #_module.Tree.Node(Lit(#_module.Stream.Nil()))
             else #_module.Tree.Node(Lit(#_module.Stream.Cons($Box(Lit(_module.__default.SkinnyFiniteTree($LS($ly), LitInt(n#0 - 1)))), 
                  Lit(#_module.Stream.Nil()))))));

procedure CheckWellformed$$_module.__default.SkinnyFiniteTree(n#0: int where LitInt(0) <= n#0);
  free requires 55 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  ensures (forall k#1: int :: 
    { _module.__default.LowerThan($LS($LS($LZ)), 
        _module.Tree.children(_module.__default.SkinnyFiniteTree($LS($LS($LZ)), n#0)), 
        k#1) } 
    LitInt(0) <= k#1
       ==> (_module.__default.LowerThan($LS($LS($LZ)), 
          _module.Tree.children(_module.__default.SkinnyFiniteTree($LS($LS($LZ)), n#0)), 
          k#1)
         <==> n#0 <= k#1));



implementation CheckWellformed$$_module.__default.SkinnyFiniteTree(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var k#2: int;
  var ##n#0: int;
  var ##s#0: DatatypeType;
  var ##n#1: int;
  var ##n#2: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function SkinnyFiniteTree
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(300,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.SkinnyFiniteTree($LS($LZ), n#0), Tclass._module.Tree());
        havoc k#2;
        assume LitInt(0) <= k#2;
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assert 0 <= n#0 || ##n#0 == n#0;
        assert n#0 == n#0 || ##n#0 < n#0;
        assume n#0 == n#0 || _module.__default.SkinnyFiniteTree#canCall(n#0);
        assume _module.Tree.Node_q(_module.__default.SkinnyFiniteTree($LS($LZ), n#0));
        assume _module.Tree.Node_q(_module.__default.SkinnyFiniteTree($LS($LZ), n#0));
        ##s#0 := _module.Tree.children(_module.__default.SkinnyFiniteTree($LS($LZ), n#0));
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        ##n#1 := k#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
        assume _module.__default.LowerThan#canCall(_module.Tree.children(_module.__default.SkinnyFiniteTree($LS($LZ), n#0)), k#2);
        assume _module.__default.LowerThan($LS($LZ), 
            _module.Tree.children(_module.__default.SkinnyFiniteTree($LS($LZ), n#0)), 
            k#2)
           <==> n#0 <= k#2;
        assume (forall k#1: int :: 
          { _module.__default.LowerThan($LS($LZ), 
              _module.Tree.children(_module.__default.SkinnyFiniteTree($LS($LZ), n#0)), 
              k#1) } 
          LitInt(0) <= k#1
             ==> (_module.__default.LowerThan($LS($LZ), 
                _module.Tree.children(_module.__default.SkinnyFiniteTree($LS($LZ), n#0)), 
                k#1)
               <==> n#0 <= k#1));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == LitInt(0))
        {
            assume _module.__default.SkinnyFiniteTree($LS($LZ), n#0)
               == Lit(#_module.Tree.Node(Lit(#_module.Stream.Nil())));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.SkinnyFiniteTree($LS($LZ), n#0), Tclass._module.Tree());
        }
        else
        {
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#2 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#2 == n#0;
            assert ##n#2 < n#0;
            assume _module.__default.SkinnyFiniteTree#canCall(n#0 - 1);
            assume _module.Tree.Node_q(_module.__default.SkinnyFiniteTree($LS($LZ), n#0 - 1));
            assume _module.__default.SkinnyFiniteTree($LS($LZ), n#0)
               == #_module.Tree.Node(#_module.Stream.Cons($Box(_module.__default.SkinnyFiniteTree($LS($LZ), n#0 - 1)), 
                  Lit(#_module.Stream.Nil())));
            assume _module.__default.SkinnyFiniteTree#canCall(n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.SkinnyFiniteTree($LS($LZ), n#0), Tclass._module.Tree());
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.FiniteUnboundedTree
function _module.__default.FiniteUnboundedTree() : DatatypeType;

function _module.__default.FiniteUnboundedTree#canCall() : bool;

// consequence axiom for _module.__default.FiniteUnboundedTree
axiom 57 <= $FunctionContextHeight
   ==> 
  _module.__default.FiniteUnboundedTree#canCall() || 57 != $FunctionContextHeight
   ==> $Is(_module.__default.FiniteUnboundedTree(), Tclass._module.Tree());

function _module.__default.FiniteUnboundedTree#requires() : bool;

// #requires axiom for _module.__default.FiniteUnboundedTree
axiom _module.__default.FiniteUnboundedTree#requires() == true;

// definition axiom for _module.__default.FiniteUnboundedTree (revealed)
axiom 57 <= $FunctionContextHeight
   ==> 
  _module.__default.FiniteUnboundedTree#canCall() || 57 != $FunctionContextHeight
   ==> _module.__default.EverLongerSkinnyTrees#canCall(LitInt(0))
     && _module.__default.FiniteUnboundedTree()
       == Lit(#_module.Tree.Node(Lit(_module.__default.EverLongerSkinnyTrees($LS($LZ), LitInt(0)))));

// definition axiom for _module.__default.FiniteUnboundedTree for all literals (revealed)
axiom 57 <= $FunctionContextHeight
   ==> 
  _module.__default.FiniteUnboundedTree#canCall() || 57 != $FunctionContextHeight
   ==> _module.__default.EverLongerSkinnyTrees#canCall(LitInt(0))
     && _module.__default.FiniteUnboundedTree()
       == Lit(#_module.Tree.Node(Lit(_module.__default.EverLongerSkinnyTrees($LS($LZ), LitInt(0)))));

procedure CheckWellformed$$_module.__default.FiniteUnboundedTree();
  free requires 57 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.FiniteUnboundedTree()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function FiniteUnboundedTree
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(309,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.FiniteUnboundedTree(), Tclass._module.Tree());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert $Is(LitInt(0), Tclass._System.nat());
        ##n#0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.EverLongerSkinnyTrees#canCall(LitInt(0));
        assume _module.__default.FiniteUnboundedTree()
           == Lit(#_module.Tree.Node(Lit(_module.__default.EverLongerSkinnyTrees($LS($LZ), LitInt(0)))));
        assume _module.__default.EverLongerSkinnyTrees#canCall(LitInt(0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.FiniteUnboundedTree(), Tclass._module.Tree());
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.EverLongerSkinnyTrees
function _module.__default.EverLongerSkinnyTrees($ly: LayerType, n#0: int) : DatatypeType;

function _module.__default.EverLongerSkinnyTrees#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.EverLongerSkinnyTrees($LS($ly), n#0) } 
  _module.__default.EverLongerSkinnyTrees($LS($ly), n#0)
     == _module.__default.EverLongerSkinnyTrees($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.EverLongerSkinnyTrees(AsFuelBottom($ly), n#0) } 
  _module.__default.EverLongerSkinnyTrees($ly, n#0)
     == _module.__default.EverLongerSkinnyTrees($LZ, n#0));

// consequence axiom for _module.__default.EverLongerSkinnyTrees
axiom 56 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.EverLongerSkinnyTrees($ly, n#0) } 
    _module.__default.EverLongerSkinnyTrees#canCall(n#0)
         || (56 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> $Is(_module.__default.EverLongerSkinnyTrees($ly, n#0), 
        Tclass._module.Stream(Tclass._module.Tree())));

function _module.__default.EverLongerSkinnyTrees#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.EverLongerSkinnyTrees
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.EverLongerSkinnyTrees#requires($ly, n#0) } 
  LitInt(0) <= n#0
     ==> _module.__default.EverLongerSkinnyTrees#requires($ly, n#0) == true);

// definition axiom for _module.__default.EverLongerSkinnyTrees (revealed)
axiom 56 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.EverLongerSkinnyTrees($LS($ly), n#0) } 
    _module.__default.EverLongerSkinnyTrees#canCall(n#0)
         || (56 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> _module.__default.SkinnyFiniteTree#canCall(n#0)
         && _module.__default.EverLongerSkinnyTrees#canCall(n#0 + 1)
         && _module.__default.EverLongerSkinnyTrees($LS($ly), n#0)
           == #_module.Stream.Cons($Box(_module.__default.SkinnyFiniteTree($LS($LZ), n#0)), 
            _module.__default.EverLongerSkinnyTrees($ly, n#0 + 1)));

procedure CheckWellformed$$_module.__default.EverLongerSkinnyTrees(n#0: int where LitInt(0) <= n#0);
  free requires 56 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.EverLongerSkinnyTrees(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##n#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function EverLongerSkinnyTrees
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(313,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.EverLongerSkinnyTrees($LS($LZ), n#0), 
          Tclass._module.Stream(Tclass._module.Tree()));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        ##n#0 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.SkinnyFiniteTree#canCall(n#0);
        assume _module.Tree.Node_q(_module.__default.SkinnyFiniteTree($LS($LZ), n#0));
        assert $Is(n#0 + 1, Tclass._System.nat());
        ##n#1 := n#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.EverLongerSkinnyTrees#canCall(n#0 + 1);
        assume _module.__default.EverLongerSkinnyTrees($LS($LZ), n#0)
           == #_module.Stream.Cons($Box(_module.__default.SkinnyFiniteTree($LS($LZ), n#0)), 
            _module.__default.EverLongerSkinnyTrees($LS($LZ), n#0 + 1));
        assume _module.__default.SkinnyFiniteTree#canCall(n#0)
           && _module.__default.EverLongerSkinnyTrees#canCall(n#0 + 1);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.EverLongerSkinnyTrees($LS($LZ), n#0), 
          Tclass._module.Stream(Tclass._module.Tree()));
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure {:_induction k#0, n#0} CheckWellformed$$_module.__default.EverLongerSkinnyTrees__Lemma(k#0: int where LitInt(0) <= k#0, n#0: int where LitInt(0) <= n#0);
  free requires 58 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction k#0, n#0} CheckWellformed$$_module.__default.EverLongerSkinnyTrees__Lemma(k#0: int, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##s#0: DatatypeType;
  var ##n#1: int;
  var ##n#2: int;
  var ##s#1: DatatypeType;
  var ##n#3: int;
  var ##n#4: int;

    // AddMethodImpl: EverLongerSkinnyTrees_Lemma, CheckWellformed$$_module.__default.EverLongerSkinnyTrees__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(318,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(319,44): post-state"} true;
    ##n#0 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
    ##s#0 := _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
    ##n#1 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
      _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
      n#0);
    assume _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), 
        $LS($LZ), 
        _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
        n#0));
    ##n#2 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
    assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
    ##s#1 := _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
    ##n#3 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
      _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
      n#0);
    assert _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), 
        $LS($LZ), 
        _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
        n#0));
    assert $Is(k#0 + n#0, Tclass._System.nat());
    ##n#4 := k#0 + n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#4, Tclass._System.nat(), $Heap);
    assume _module.__default.SkinnyFiniteTree#canCall(k#0 + n#0);
    assume _module.Tree.Node_q(_module.__default.SkinnyFiniteTree($LS($LZ), k#0 + n#0));
    assume _module.Tree#Equal($Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), 
            $LS($LZ), 
            _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
            n#0))): DatatypeType, 
      _module.__default.SkinnyFiniteTree($LS($LZ), k#0 + n#0));
}



procedure {:_induction k#0, n#0} Call$$_module.__default.EverLongerSkinnyTrees__Lemma(k#0: int where LitInt(0) <= k#0, n#0: int where LitInt(0) <= n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.EverLongerSkinnyTrees#canCall(k#0)
     && _module.__default.Tail#canCall(Tclass._module.Tree(), 
      _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
      n#0);
  ensures _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), 
      $LS($LS($LZ)), 
      _module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0), 
      n#0));
  free ensures $IsA#_module.Tree($Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), 
            $LS($LZ), 
            _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
            n#0))): DatatypeType)
     && $IsA#_module.Tree(_module.__default.SkinnyFiniteTree($LS($LZ), k#0 + n#0))
     && 
    _module.__default.EverLongerSkinnyTrees#canCall(k#0)
     && _module.__default.Tail#canCall(Tclass._module.Tree(), 
      _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
      n#0)
     && _module.__default.SkinnyFiniteTree#canCall(k#0 + n#0);
  ensures _module.Tree#Equal($Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), 
          $LS($LS($LZ)), 
          _module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0), 
          n#0))): DatatypeType, 
    _module.__default.SkinnyFiniteTree($LS($LS($LZ)), k#0 + n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0, n#0} Impl$$_module.__default.EverLongerSkinnyTrees__Lemma(k#0: int where LitInt(0) <= k#0, n#0: int where LitInt(0) <= n#0)
   returns ($_reverifyPost: bool);
  free requires 58 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.EverLongerSkinnyTrees#canCall(k#0)
     && _module.__default.Tail#canCall(Tclass._module.Tree(), 
      _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
      n#0);
  ensures _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), 
      $LS($LS($LZ)), 
      _module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0), 
      n#0));
  free ensures $IsA#_module.Tree($Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), 
            $LS($LZ), 
            _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
            n#0))): DatatypeType)
     && $IsA#_module.Tree(_module.__default.SkinnyFiniteTree($LS($LZ), k#0 + n#0))
     && 
    _module.__default.EverLongerSkinnyTrees#canCall(k#0)
     && _module.__default.Tail#canCall(Tclass._module.Tree(), 
      _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
      n#0)
     && _module.__default.SkinnyFiniteTree#canCall(k#0 + n#0);
  ensures _module.Tree#Equal($Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), 
          $LS($LS($LZ)), 
          _module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0), 
          n#0))): DatatypeType, 
    _module.__default.SkinnyFiniteTree($LS($LS($LZ)), k#0 + n#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0, n#0} Impl$$_module.__default.EverLongerSkinnyTrees__Lemma(k#0: int, n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##n#1_0_0: int;
  var ##s#1_0_0: DatatypeType;
  var ##n#1_0_1: int;
  var ##n#1_0_2: int;
  var ##s#1_0_1: DatatypeType;
  var ##n#1_0_3: int;
  var ##n#1_1_0: int;
  var ##s#1_1_0: DatatypeType;
  var ##n#1_1_1: int;
  var s##1_1_0: DatatypeType;
  var ##n#1_1_2: int;
  var n##1_1_0: int;
  var ##n#1_1_3: int;
  var ##s#1_1_1: DatatypeType;
  var ##n#1_1_4: int;
  var ##n#1_2_0: int;
  var ##s#1_2_0: DatatypeType;
  var ##n#1_2_1: int;
  var k##1_2_0: int;
  var n##1_2_0: int;
  var ##n#1_2_2: int;
  var ##s#1_2_1: DatatypeType;
  var ##n#1_2_3: int;
  var ##n#1_0: int;
  var ##s#1_0: DatatypeType;
  var ##n#1_1: int;
  var k##0: int;
  var n##0: int;

    // AddMethodImpl: EverLongerSkinnyTrees_Lemma, Impl$$_module.__default.EverLongerSkinnyTrees__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(322,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int, $ih#n0#0: int :: 
      LitInt(0) <= $ih#k0#0
           && LitInt(0) <= $ih#n0#0
           && Lit(true)
           && 
          0 <= $ih#n0#0
           && $ih#n0#0 < n#0
         ==> _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), 
              $LS($LZ), 
              _module.__default.EverLongerSkinnyTrees($LS($LZ), $ih#k0#0), 
              $ih#n0#0))
           && _module.Tree#Equal($Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), 
                  $LS($LZ), 
                  _module.__default.EverLongerSkinnyTrees($LS($LZ), $ih#k0#0), 
                  $ih#n0#0))): DatatypeType, 
            _module.__default.SkinnyFiniteTree($LS($LZ), $ih#k0#0 + $ih#n0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(323,3)
    assume true;
    if (n#0 == LitInt(0))
    {
    }
    else
    {
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            ##n#1_0 := k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0, Tclass._System.nat(), $Heap);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
            ##s#1_0 := _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#1_1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
              _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
              n#0);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0)
               && _module.__default.Tail#canCall(Tclass._module.Tree(), 
                _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
                n#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            ##n#1_2_0 := k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_2_0, Tclass._System.nat(), $Heap);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
            ##s#1_2_0 := _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_2_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##n#1_2_1 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_2_1, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
              _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
              n#0);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0)
               && _module.__default.Tail#canCall(Tclass._module.Tree(), 
                _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
                n#0);
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(327,36)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            k##1_2_0 := k#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0 - 1, Tclass._System.nat());
            n##1_2_0 := n#0 - 1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || n##1_2_0 == n#0;
            assert n##1_2_0 < n#0;
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.EverLongerSkinnyTrees__Lemma(k##1_2_0, n##1_2_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(327,43)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            ##n#1_2_2 := k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_2_2, Tclass._System.nat(), $Heap);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
            ##s#1_2_1 := _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_2_1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_2_3 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_2_3, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
              _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
              n#0 - 1);
            assert _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), 
                $LS($LZ), 
                _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
                n#0 - 1));
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0)
               && _module.__default.Tail#canCall(Tclass._module.Tree(), 
                _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
                n#0 - 1);
            // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            assert {:subsumption 0} $Eq#_module.Stream(Tclass._module.Tree(), 
              Tclass._module.Tree(), 
              $LS($LS($LZ)), 
              _module.__default.Tail(Tclass._module.Tree(), 
                $LS($LS($LZ)), 
                _module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0), 
                n#0), 
              _module.Stream.tail(_module.__default.Tail(Tclass._module.Tree(), 
                  $LS($LS($LZ)), 
                  _module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0), 
                  n#0 - 1)));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            ##n#1_1_0 := k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_0, Tclass._System.nat(), $Heap);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
            ##s#1_1_0 := _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_1_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_1_1 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_1, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
              _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
              n#0 - 1);
            assume _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), 
                $LS($LZ), 
                _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
                n#0 - 1));
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0)
               && _module.__default.Tail#canCall(Tclass._module.Tree(), 
                _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
                n#0 - 1);
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(329,20)
            // TrCallStmt: Before ProcessCallStmt
            ##n#1_1_2 := k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_2, Tclass._System.nat(), $Heap);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
            // ProcessCallStmt: CheckSubrange
            s##1_1_0 := _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0 - 1, Tclass._System.nat());
            n##1_1_0 := n#0 - 1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Tail__Lemma0(Tclass._module.Tree(), s##1_1_0, n##1_1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(329,50)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            ##n#1_1_3 := k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_3, Tclass._System.nat(), $Heap);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
            assert _module.Stream.Cons_q(_module.__default.EverLongerSkinnyTrees($LS($LZ), k#0));
            ##s#1_1_1 := _module.Stream.tail(_module.__default.EverLongerSkinnyTrees($LS($LZ), k#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_1_1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_1_4 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_4, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
              _module.Stream.tail(_module.__default.EverLongerSkinnyTrees($LS($LZ), k#0)), 
              n#0 - 1);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0)
               && _module.__default.Tail#canCall(Tclass._module.Tree(), 
                _module.Stream.tail(_module.__default.EverLongerSkinnyTrees($LS($LZ), k#0)), 
                n#0 - 1);
            // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            assert {:subsumption 0} $Eq#_module.Stream(Tclass._module.Tree(), 
              Tclass._module.Tree(), 
              $LS($LS($LZ)), 
              _module.Stream.tail(_module.__default.Tail(Tclass._module.Tree(), 
                  $LS($LS($LZ)), 
                  _module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0), 
                  n#0 - 1)), 
              _module.__default.Tail(Tclass._module.Tree(), 
                $LS($LS($LZ)), 
                _module.Stream.tail(_module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0)), 
                n#0 - 1));
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            ##n#1_0_0 := k#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0_0, Tclass._System.nat(), $Heap);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0);
            assume _module.Stream.Cons_q(_module.__default.EverLongerSkinnyTrees($LS($LZ), k#0));
            ##s#1_0_0 := _module.Stream.tail(_module.__default.EverLongerSkinnyTrees($LS($LZ), k#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_0_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assume $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_0_1 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0_1, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
              _module.Stream.tail(_module.__default.EverLongerSkinnyTrees($LS($LZ), k#0)), 
              n#0 - 1);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0)
               && _module.__default.Tail#canCall(Tclass._module.Tree(), 
                _module.Stream.tail(_module.__default.EverLongerSkinnyTrees($LS($LZ), k#0)), 
                n#0 - 1);
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            assert $Is(k#0 + 1, Tclass._System.nat());
            ##n#1_0_2 := k#0 + 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0_2, Tclass._System.nat(), $Heap);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0 + 1);
            ##s#1_0_1 := _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0 + 1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_0_1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_0_3 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0_3, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(Tclass._module.Tree(), 
              _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0 + 1), 
              n#0 - 1);
            assume _module.__default.EverLongerSkinnyTrees#canCall(k#0 + 1)
               && _module.__default.Tail#canCall(Tclass._module.Tree(), 
                _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0 + 1), 
                n#0 - 1);
            // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(325,5)
            assert {:subsumption 0} $Eq#_module.Stream(Tclass._module.Tree(), 
              Tclass._module.Tree(), 
              $LS($LS($LZ)), 
              _module.__default.Tail(Tclass._module.Tree(), 
                $LS($LS($LZ)), 
                _module.Stream.tail(_module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0)), 
                n#0 - 1), 
              _module.__default.Tail(Tclass._module.Tree(), 
                $LS($LS($LZ)), 
                _module.__default.EverLongerSkinnyTrees($LS($LS($LZ)), k#0 + 1), 
                n#0 - 1));
            assume false;
        }

        assume $Eq#_module.Stream(Tclass._module.Tree(), 
          Tclass._module.Tree(), 
          $LS($LS($LZ)), 
          _module.__default.Tail(Tclass._module.Tree(), 
            $LS($LZ), 
            _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0), 
            n#0), 
          _module.__default.Tail(Tclass._module.Tree(), 
            $LS($LZ), 
            _module.__default.EverLongerSkinnyTrees($LS($LZ), k#0 + 1), 
            n#0 - 1));
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(333,32)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(k#0 + 1, Tclass._System.nat());
        k##0 := k#0 + 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0 - 1, Tclass._System.nat());
        n##0 := n#0 - 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= n#0 || n##0 == n#0;
        assert n##0 < n#0;
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.EverLongerSkinnyTrees__Lemma(k##0, n##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(333,41)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Proposition3();
  free requires 70 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Proposition3();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FiniteUnboundedTree#canCall()
     && _module.__default.HasBoundedHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()))
     && (!Lit(_module.__default.HasBoundedHeight(Lit(_module.__default.FiniteUnboundedTree())))
       ==> _module.__default.FiniteUnboundedTree#canCall()
         && _module.__default.HasFiniteHeight#canCall(Lit(_module.__default.FiniteUnboundedTree())));
  ensures !Lit(_module.__default.HasBoundedHeight(Lit(_module.__default.FiniteUnboundedTree())));
  free ensures _module.__default.HasFiniteHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()))
     && 
    Lit(_module.__default.HasFiniteHeight(Lit(_module.__default.FiniteUnboundedTree())))
     && (forall p#0: DatatypeType :: 
      { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0) } 
        { _module.__default.ValidPath($LS($LZ), _module.__default.FiniteUnboundedTree(), p#0) } 
      $Is(p#0, Tclass._module.Stream(TInt))
         ==> 
        _module.__default.ValidPath($LS($LZ), Lit(_module.__default.FiniteUnboundedTree()), p#0)
         ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Proposition3() returns ($_reverifyPost: bool);
  free requires 70 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FiniteUnboundedTree#canCall()
     && _module.__default.HasBoundedHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()))
     && (!Lit(_module.__default.HasBoundedHeight(Lit(_module.__default.FiniteUnboundedTree())))
       ==> _module.__default.FiniteUnboundedTree#canCall()
         && _module.__default.HasFiniteHeight#canCall(Lit(_module.__default.FiniteUnboundedTree())));
  ensures !Lit(_module.__default.HasBoundedHeight(Lit(_module.__default.FiniteUnboundedTree())));
  ensures _module.__default.HasFiniteHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()))
     ==> Lit(_module.__default.HasFiniteHeight(Lit(_module.__default.FiniteUnboundedTree())))
       || (forall p#1: DatatypeType :: 
        { _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1) } 
          { _module.__default.ValidPath($LS($LS($LZ)), _module.__default.FiniteUnboundedTree(), p#1) } 
        $Is(p#1, Tclass._module.Stream(TInt))
           ==> 
          _module.__default.ValidPath($LS($LS($LZ)), Lit(_module.__default.FiniteUnboundedTree()), p#1)
           ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Proposition3() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Proposition3, Impl$$_module.__default.Proposition3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(339,0): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(340,16)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Proposition3a();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(340,17)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(341,16)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Proposition3b();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(341,17)"} true;
}



procedure CheckWellformed$$_module.__default.Proposition3a();
  free requires 68 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Proposition3a();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FiniteUnboundedTree#canCall()
     && _module.__default.HasBoundedHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()));
  ensures !Lit(_module.__default.HasBoundedHeight(Lit(_module.__default.FiniteUnboundedTree())));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Proposition3a() returns ($_reverifyPost: bool);
  free requires 68 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FiniteUnboundedTree#canCall()
     && _module.__default.HasBoundedHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()));
  ensures !Lit(_module.__default.HasBoundedHeight(Lit(_module.__default.FiniteUnboundedTree())));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Proposition3a() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ch#0: DatatypeType
     where $Is(ch#0, Tclass._module.Stream(Tclass._module.Tree()))
       && $IsAlloc(ch#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
  var n#0: int;
  var cn#0: DatatypeType
     where $Is(cn#0, Tclass._module.Stream(Tclass._module.Tree()))
       && $IsAlloc(cn#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var k##0: int;
  var n##0: int;
  var ##n#1: int;
  var ##s#1: DatatypeType;
  var ##n#2: int;
  var s##0: DatatypeType;
  var n##1: int;
  var h##0: int;

    // AddMethodImpl: Proposition3a, Impl$$_module.__default.Proposition3a
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(345,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(346,10)
    assume true;
    assume _module.__default.FiniteUnboundedTree#canCall();
    assume _module.Tree.Node_q(Lit(_module.__default.FiniteUnboundedTree()));
    assume _module.Tree.Node_q(Lit(_module.__default.FiniteUnboundedTree()));
    assume _module.__default.FiniteUnboundedTree#canCall()
       && _module.Tree.Node_q(Lit(_module.__default.FiniteUnboundedTree()));
    ch#0 := Lit(_module.Tree.children(Lit(_module.__default.FiniteUnboundedTree())));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(346,42)"} true;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(347,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc n#0;
        assume true;
        assume true;
        assume LitInt(0) <= n#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(350,12)
        assume true;
        ##s#0 := ch#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        assert $Is(n#0 + 1, Tclass._System.nat());
        ##n#0 := n#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(Tclass._module.Tree(), ch#0, n#0 + 1);
        assume _module.__default.Tail#canCall(Tclass._module.Tree(), ch#0, n#0 + 1);
        cn#0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), ch#0, n#0 + 1);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(350,27)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(351,32)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(LitInt(0), Tclass._System.nat());
        k##0 := LitInt(0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0 + 1, Tclass._System.nat());
        n##0 := n#0 + 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.EverLongerSkinnyTrees__Lemma(k##0, n##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(351,39)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(352,5)
        assert _module.Stream.Cons_q(cn#0);
        assert $Is(n#0 + 1, Tclass._System.nat());
        ##n#1 := n#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
        assume _module.__default.SkinnyFiniteTree#canCall(n#0 + 1);
        assume _module.Tree.Node_q(_module.__default.SkinnyFiniteTree($LS($LZ), n#0 + 1));
        assume $IsA#_module.Tree($Unbox(_module.Stream.head(cn#0)): DatatypeType)
           && $IsA#_module.Tree(_module.__default.SkinnyFiniteTree($LS($LZ), n#0 + 1))
           && _module.__default.SkinnyFiniteTree#canCall(n#0 + 1);
        assert {:subsumption 0} _module.Tree#Equal($Unbox(_module.Stream.head(cn#0)): DatatypeType, 
          _module.__default.SkinnyFiniteTree($LS($LS($LZ)), n#0 + 1));
        assume _module.Tree#Equal($Unbox(_module.Stream.head(cn#0)): DatatypeType, 
          _module.__default.SkinnyFiniteTree($LS($LS($LZ)), n#0 + 1));
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(353,5)
        assert _module.Stream.Cons_q(cn#0);
        assume _module.Tree.Node_q($Unbox(_module.Stream.head(cn#0)): DatatypeType);
        ##s#1 := _module.Tree.children($Unbox(_module.Stream.head(cn#0)): DatatypeType);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        assert $Is(n#0, Tclass._System.nat());
        ##n#2 := n#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
        assume _module.__default.LowerThan#canCall(_module.Tree.children($Unbox(_module.Stream.head(cn#0)): DatatypeType), n#0);
        assume _module.Tree.Node_q($Unbox(_module.Stream.head(cn#0)): DatatypeType)
           && _module.__default.LowerThan#canCall(_module.Tree.children($Unbox(_module.Stream.head(cn#0)): DatatypeType), n#0);
        assert {:subsumption 0} !_module.__default.LowerThan($LS($LS($LZ)), 
          _module.Tree.children($Unbox(_module.Stream.head(cn#0)): DatatypeType), 
          n#0);
        assume !_module.__default.LowerThan($LS($LZ), 
          _module.Tree.children($Unbox(_module.Stream.head(cn#0)): DatatypeType), 
          n#0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(354,20)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := ch#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0 + 1, Tclass._System.nat());
        n##1 := n#0 + 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0, Tclass._System.nat());
        h##0 := n#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.LowerThan__Lemma(s##0, n##1, h##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(354,31)"} true;
        assert !_module.__default.LowerThan($LS($LS($LZ)), ch#0, n#0);
        assume false;
    }
    else
    {
        assume (forall n#1: int :: 
          { _module.__default.LowerThan($LS($LZ), ch#0, n#1) } 
          LitInt(0) <= n#1 ==> !_module.__default.LowerThan($LS($LZ), ch#0, n#1));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(355,2)"} true;
}



procedure CheckWellformed$$_module.__default.Proposition3b();
  free requires 69 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Proposition3b();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FiniteUnboundedTree#canCall()
     && _module.__default.HasFiniteHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()));
  free ensures _module.__default.HasFiniteHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()))
     && 
    Lit(_module.__default.HasFiniteHeight(Lit(_module.__default.FiniteUnboundedTree())))
     && (forall p#0: DatatypeType :: 
      { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0) } 
        { _module.__default.ValidPath($LS($LZ), _module.__default.FiniteUnboundedTree(), p#0) } 
      $Is(p#0, Tclass._module.Stream(TInt))
         ==> 
        _module.__default.ValidPath($LS($LZ), Lit(_module.__default.FiniteUnboundedTree()), p#0)
         ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Proposition3b() returns ($_reverifyPost: bool);
  free requires 69 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.FiniteUnboundedTree#canCall()
     && _module.__default.HasFiniteHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()));
  ensures _module.__default.HasFiniteHeight#canCall(Lit(_module.__default.FiniteUnboundedTree()))
     ==> Lit(_module.__default.HasFiniteHeight(Lit(_module.__default.FiniteUnboundedTree())))
       || (forall p#1: DatatypeType :: 
        { _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1) } 
          { _module.__default.ValidPath($LS($LS($LZ)), _module.__default.FiniteUnboundedTree(), p#1) } 
        $Is(p#1, Tclass._module.Stream(TInt))
           ==> 
          _module.__default.ValidPath($LS($LS($LZ)), Lit(_module.__default.FiniteUnboundedTree()), p#1)
           ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Proposition3b() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#0: DatatypeType
     where $Is(t#0, Tclass._module.Tree()) && $IsAlloc(t#0, Tclass._module.Tree(), $Heap);
  var p#2: DatatypeType;
  var ##t#1: DatatypeType;
  var ##p#0: DatatypeType;
  var index#0: int;
  var ch#0: DatatypeType
     where $Is(ch#0, Tclass._module.Stream(Tclass._module.Tree()))
       && $IsAlloc(ch#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var ##t#2: DatatypeType;
  var ##p#1: DatatypeType;
  var k##0: int;
  var n##0: int;
  var ##n#1: int;
  var si#0: DatatypeType
     where $Is(si#0, Tclass._module.Tree()) && $IsAlloc(si#0, Tclass._module.Tree(), $Heap);
  var ##n#2: int;
  var ##s#1: DatatypeType;
  var ##n#3: int;
  var t##0: DatatypeType;
  var h##0: int;
  var p##0: DatatypeType;

    // AddMethodImpl: Proposition3b, Impl$$_module.__default.Proposition3b
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(359,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(360,9)
    assume true;
    assume _module.__default.FiniteUnboundedTree#canCall();
    assume _module.Tree.Node_q(Lit(_module.__default.FiniteUnboundedTree()));
    assume _module.__default.FiniteUnboundedTree#canCall();
    t#0 := Lit(_module.__default.FiniteUnboundedTree());
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(360,32)"} true;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(361,3)
    if (*)
    {
        // Assume Fuel Constant
        havoc p#2;
        assume $Is(p#2, Tclass._module.Stream(TInt));
        ##t#1 := t#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#1, Tclass._module.Tree(), $Heap);
        ##p#0 := p#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#0, Tclass._module.Stream(TInt), $Heap);
        assume _module.__default.ValidPath#canCall(t#0, p#2);
        assume _module.__default.ValidPath#canCall(t#0, p#2);
        assume _module.__default.ValidPath($LS($LZ), t#0, p#2);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(364,5)
        assume true;
        assert _module.Stream.Cons_q(p#2);
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(365,15)
        assume true;
        assert _module.Stream.Cons_q(p#2);
        assume true;
        index#0 := $Unbox(_module.Stream.head(p#2)): int;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(365,23)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(366,5)
        assume true;
        assert LitInt(0) <= index#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(367,12)
        assume true;
        assume _module.Tree.Node_q(t#0);
        ##s#0 := _module.Tree.children(t#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        assert $Is(index#0, Tclass._System.nat());
        ##n#0 := index#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#0);
        assume _module.Tree.Node_q(t#0)
           && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#0);
        ch#0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(367,37)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(368,5)
        if (_module.Stream.Cons_q(ch#0))
        {
            assert _module.Stream.Cons_q(ch#0);
            assert _module.Stream.Cons_q(p#2);
            ##t#2 := $Unbox(_module.Stream.head(ch#0)): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
            ##p#1 := _module.Stream.tail(p#2);
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#1, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.ValidPath#canCall($Unbox(_module.Stream.head(ch#0)): DatatypeType, _module.Stream.tail(p#2));
        }

        assume _module.Stream.Cons_q(ch#0)
           ==> _module.__default.ValidPath#canCall($Unbox(_module.Stream.head(ch#0)): DatatypeType, _module.Stream.tail(p#2));
        assert {:subsumption 0} _module.Stream.Cons_q(ch#0);
        assert {:subsumption 0} _module.__default.ValidPath($LS($LS($LZ)), 
          $Unbox(_module.Stream.head(ch#0)): DatatypeType, 
          _module.Stream.tail(p#2));
        assume _module.Stream.Cons_q(ch#0)
           && _module.__default.ValidPath($LS($LZ), 
            $Unbox(_module.Stream.head(ch#0)): DatatypeType, 
            _module.Stream.tail(p#2));
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(369,32)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(LitInt(0), Tclass._System.nat());
        k##0 := LitInt(0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(index#0, Tclass._System.nat());
        n##0 := index#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.EverLongerSkinnyTrees__Lemma(k##0, n##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(369,41)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(370,5)
        assert _module.Stream.Cons_q(ch#0);
        assert $Is(index#0, Tclass._System.nat());
        ##n#1 := index#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
        assume _module.__default.SkinnyFiniteTree#canCall(index#0);
        assume _module.Tree.Node_q(_module.__default.SkinnyFiniteTree($LS($LZ), index#0));
        assume $IsA#_module.Tree($Unbox(_module.Stream.head(ch#0)): DatatypeType)
           && $IsA#_module.Tree(_module.__default.SkinnyFiniteTree($LS($LZ), index#0))
           && _module.__default.SkinnyFiniteTree#canCall(index#0);
        assert {:subsumption 0} _module.Tree#Equal($Unbox(_module.Stream.head(ch#0)): DatatypeType, 
          _module.__default.SkinnyFiniteTree($LS($LS($LZ)), index#0));
        assume _module.Tree#Equal($Unbox(_module.Stream.head(ch#0)): DatatypeType, 
          _module.__default.SkinnyFiniteTree($LS($LS($LZ)), index#0));
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(371,12)
        assume true;
        assert $Is(index#0, Tclass._System.nat());
        ##n#2 := index#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
        assume _module.__default.SkinnyFiniteTree#canCall(index#0);
        assume _module.Tree.Node_q(_module.__default.SkinnyFiniteTree($LS($LZ), index#0));
        assume _module.__default.SkinnyFiniteTree#canCall(index#0);
        si#0 := _module.__default.SkinnyFiniteTree($LS($LZ), index#0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(371,37)"} true;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(372,5)
        assume _module.Tree.Node_q(si#0);
        ##s#1 := _module.Tree.children(si#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        assert $Is(index#0, Tclass._System.nat());
        ##n#3 := index#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
        assume _module.__default.LowerThan#canCall(_module.Tree.children(si#0), index#0);
        assume _module.Tree.Node_q(si#0)
           && _module.__default.LowerThan#canCall(_module.Tree.children(si#0), index#0);
        assert {:subsumption 0} _module.__default.LowerThan($LS($LS($LZ)), _module.Tree.children(si#0), index#0);
        assume _module.__default.LowerThan($LS($LZ), _module.Tree.children(si#0), index#0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(373,24)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0 := si#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(index#0, Tclass._System.nat());
        h##0 := index#0;
        assert _module.Stream.Cons_q(p#2);
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0 := _module.Stream.tail(p#2);
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Proposition3b__Lemma(t##0, h##0, p##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(373,42)"} true;
        assert !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#2);
        assume false;
    }
    else
    {
        assume (forall p#3: DatatypeType :: 
          { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#3) } 
            { _module.__default.ValidPath($LS($LZ), t#0, p#3) } 
          $Is(p#3, Tclass._module.Stream(TInt))
               && _module.__default.ValidPath($LS($LZ), t#0, p#3)
             ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#3));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(374,2)"} true;
}



procedure {:_induction t#0, h#0, p#0} CheckWellformed$$_module.__default.Proposition3b__Lemma(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    h#0: int where LitInt(0) <= h#0, 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  free requires 59 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction t#0, h#0, p#0} Call$$_module.__default.Proposition3b__Lemma(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    h#0: int where LitInt(0) <= h#0, 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  // user-defined preconditions
  requires _module.__default.LowerThan($LS($LS($LZ)), _module.Tree.children(t#0), h#0);
  requires _module.__default.ValidPath($LS($LS($LZ)), t#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
  ensures !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction t#0, h#0, p#0} Impl$$_module.__default.Proposition3b__Lemma(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    h#0: int where LitInt(0) <= h#0, 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0))
   returns ($_reverifyPost: bool);
  free requires 59 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.LowerThan($LS($LS($LZ)), _module.Tree.children(t#0), h#0);
  requires _module.__default.ValidPath($LS($LS($LZ)), t#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
  ensures !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction t#0, h#0, p#0} Impl$$_module.__default.Proposition3b__Lemma(t#0: DatatypeType, h#0: int, p#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0_0: int;
  var _mcc#1#0_0: DatatypeType;
  var tail#0_0: DatatypeType;
  var let#0_0#0#0: DatatypeType;
  var index#0_0: int;
  var let#0_1#0#0: int;
  var ch#0_0: DatatypeType
     where $Is(ch#0_0, Tclass._module.Stream(Tclass._module.Tree()))
       && $IsAlloc(ch#0_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
  var ##s#0_0: DatatypeType;
  var ##n#0_0: int;
  var _mcc#2#0_0_0: DatatypeType;
  var _mcc#3#0_0_0: DatatypeType;
  var s##0_0_0: DatatypeType;
  var n##0_0_0: int;
  var h##0_0_0: int;
  var p##0_1_0: DatatypeType;
  var ##s#0_1: DatatypeType;
  var ##n#0_1: int;

    // AddMethodImpl: Proposition3b_Lemma, Impl$$_module.__default.Proposition3b__Lemma
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(380,0): initial state"} true;
    assume $IsA#_module.Tree(t#0);
    assume $IsA#_module.Stream(p#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#t0#0: DatatypeType, $ih#h0#0: int, $ih#p0#0: DatatypeType :: 
      $Is($ih#t0#0, Tclass._module.Tree())
           && LitInt(0) <= $ih#h0#0
           && $Is($ih#p0#0, Tclass._module.Stream(TInt))
           && 
          _module.__default.LowerThan($LS($LZ), _module.Tree.children($ih#t0#0), $ih#h0#0)
           && _module.__default.ValidPath($LS($LZ), $ih#t0#0, $ih#p0#0)
           && 
          0 <= $ih#h0#0
           && $ih#h0#0 < h#0
         ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), $ih#p0#0));
    $_reverifyPost := false;
    assume true;
    havoc _mcc#0#0_0, _mcc#1#0_0;
    if (p#0 == #_module.Stream.Nil())
    {
    }
    else if (p#0 == #_module.Stream.Cons($Box(_mcc#0#0_0), _mcc#1#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass._module.Stream(TInt));
        havoc tail#0_0;
        assume $Is(tail#0_0, Tclass._module.Stream(TInt))
           && $IsAlloc(tail#0_0, Tclass._module.Stream(TInt), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass._module.Stream(TInt));
        assume tail#0_0 == let#0_0#0#0;
        havoc index#0_0;
        assume let#0_1#0#0 == _mcc#0#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_1#0#0, TInt);
        assume index#0_0 == let#0_1#0#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(385,14)
        assume true;
        assume _module.Tree.Node_q(t#0);
        ##s#0_0 := _module.Tree.children(t#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        assert $Is(index#0_0, Tclass._System.nat());
        ##n#0_0 := index#0_0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_0, Tclass._System.nat(), $Heap);
        assume _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#0_0);
        assume _module.Tree.Node_q(t#0)
           && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#0), index#0_0);
        ch#0_0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#0), index#0_0);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(385,39)"} true;
        assume _module.Tree.Node_q(t#0);
        assume _module.Tree.Node_q(t#0);
        havoc _mcc#2#0_0_0, _mcc#3#0_0_0;
        if (_module.Tree.children(t#0) == #_module.Stream.Nil())
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(390,26)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            p##0_1_0 := p#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.ValidPath__Lemma(p##0_1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(390,28)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(391,11)
            assume true;
            assert false;
        }
        else if (_module.Tree.children(t#0)
           == #_module.Stream.Cons($Box(_mcc#2#0_0_0), _mcc#3#0_0_0))
        {
            assume $Is(_mcc#2#0_0_0, Tclass._module.Tree());
            assume $Is(_mcc#3#0_0_0, Tclass._module.Stream(Tclass._module.Tree()));
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(394,26)
            // TrCallStmt: Before ProcessCallStmt
            assume _module.Tree.Node_q(t#0);
            assume _module.Tree.Node_q(t#0);
            // ProcessCallStmt: CheckSubrange
            s##0_0_0 := _module.Tree.children(t#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(index#0_0, Tclass._System.nat());
            n##0_0_0 := index#0_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            h##0_0_0 := h#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.LowerThan__Lemma(s##0_0_0, n##0_0_0, h##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(394,47)"} true;
        }
        else
        {
            assume false;
        }

        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(398,7)
        assert _module.Stream.Cons_q(ch#0_0);
        assume _module.Tree.Node_q($Unbox(_module.Stream.head(ch#0_0)): DatatypeType);
        ##s#0_1 := _module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0_1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
        assert $Is(h#0 - 1, Tclass._System.nat());
        ##n#0_1 := h#0 - 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0_1, Tclass._System.nat(), $Heap);
        assume _module.__default.LowerThan#canCall(_module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
          h#0 - 1);
        assume _module.Tree.Node_q($Unbox(_module.Stream.head(ch#0_0)): DatatypeType)
           && _module.__default.LowerThan#canCall(_module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
            h#0 - 1);
        assert {:subsumption 0} _module.__default.LowerThan($LS($LS($LZ)), 
          _module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
          h#0 - 1);
        assume _module.__default.LowerThan($LS($LZ), 
          _module.Tree.children($Unbox(_module.Stream.head(ch#0_0)): DatatypeType), 
          h#0 - 1);
    }
    else
    {
        assume false;
    }
}



// function declaration for _module._default.InfinitePath
function _module.__default.InfinitePath($ly: LayerType, r#0: DatatypeType) : bool;

function _module.__default.InfinitePath#canCall(r#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, r#0: DatatypeType :: 
  { _module.__default.InfinitePath($LS($ly), r#0) } 
  _module.__default.InfinitePath($LS($ly), r#0)
     == _module.__default.InfinitePath($ly, r#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, r#0: DatatypeType :: 
  { _module.__default.InfinitePath(AsFuelBottom($ly), r#0) } 
  _module.__default.InfinitePath($ly, r#0)
     == _module.__default.InfinitePath($LZ, r#0));

// consequence axiom for _module.__default.InfinitePath
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, r#0: DatatypeType :: 
    { _module.__default.InfinitePath($ly, r#0) } 
    _module.__default.InfinitePath#canCall(r#0)
         || (24 != $FunctionContextHeight
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> true);

function _module.__default.InfinitePath#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.InfinitePath
axiom (forall $ly: LayerType, r#0: DatatypeType :: 
  { _module.__default.InfinitePath#requires($ly, r#0) } 
  $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
     ==> _module.__default.InfinitePath#requires($ly, r#0) == true);

// definition axiom for _module.__default.InfinitePath (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, r#0: DatatypeType :: 
    { _module.__default.InfinitePath($LS($ly), r#0) } 
    _module.__default.InfinitePath#canCall(r#0)
         || (24 != $FunctionContextHeight
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (!_module.CoOption.None_q(r#0)
           ==> (var num#1 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
            _module.__default.InfinitePath_k#canCall(num#1)))
         && _module.__default.InfinitePath($LS($ly), r#0)
           == (if _module.CoOption.None_q(r#0)
             then false
             else (var num#0 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.InfinitePath_k($ly, num#0))));

// 1st prefix predicate axiom for _module.__default.InfinitePath_h
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, r#0: DatatypeType :: 
    { _module.__default.InfinitePath($LS($ly), r#0) } 
    $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && _module.__default.InfinitePath($LS($ly), r#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.InfinitePath_h($LS($ly), _k#0, r#0) } 
        _module.__default.InfinitePath_h($LS($ly), _k#0, r#0)));

// 2nd prefix predicate axiom
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, r#0: DatatypeType :: 
    { _module.__default.InfinitePath($LS($ly), r#0) } 
    $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && (forall _k#0: Box :: 
          { _module.__default.InfinitePath_h($LS($ly), _k#0, r#0) } 
          _module.__default.InfinitePath_h($LS($ly), _k#0, r#0))
       ==> _module.__default.InfinitePath($LS($ly), r#0));

// 3rd prefix predicate axiom
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, r#0: DatatypeType, _k#0: Box :: 
    { _module.__default.InfinitePath_h($ly, _k#0, r#0) } 
    $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.InfinitePath_h($ly, _k#0, r#0));

procedure CheckWellformed$$_module.__default.InfinitePath(r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.InfinitePath(r#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var num#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##num#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function InfinitePath
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(434,19): initial state"} true;
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
        if (r#0 == #_module.CoOption.None())
        {
            assume _module.__default.InfinitePath($LS($LZ), r#0) == Lit(false);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.InfinitePath($LS($LZ), r#0), TBool);
        }
        else if (r#0 == #_module.CoOption.Some($Box(_mcc#0#0)))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number());
            havoc num#Z#0;
            assume $Is(num#Z#0, Tclass._module.Number());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Number());
            assume num#Z#0 == let#0#0#0;
            ##num#0 := num#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.InfinitePath_k#canCall(num#Z#0);
            assume _module.__default.InfinitePath($LS($LZ), r#0)
               == _module.__default.InfinitePath_k($LS($LZ), num#Z#0);
            assume _module.__default.InfinitePath_k#canCall(num#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.InfinitePath($LS($LZ), r#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.InfinitePath#
function _module.__default.InfinitePath_h($ly: LayerType, _k#0: Box, r#0: DatatypeType) : bool;

function _module.__default.InfinitePath_h#canCall(_k#0: Box, r#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, r#0: DatatypeType :: 
  { _module.__default.InfinitePath_h($LS($ly), _k#0, r#0) } 
  _module.__default.InfinitePath_h($LS($ly), _k#0, r#0)
     == _module.__default.InfinitePath_h($ly, _k#0, r#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, r#0: DatatypeType :: 
  { _module.__default.InfinitePath_h(AsFuelBottom($ly), _k#0, r#0) } 
  _module.__default.InfinitePath_h($ly, _k#0, r#0)
     == _module.__default.InfinitePath_h($LZ, _k#0, r#0));

// consequence axiom for _module.__default.InfinitePath_h
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, r#0: DatatypeType :: 
    { _module.__default.InfinitePath_h($ly, _k#0, r#0) } 
    _module.__default.InfinitePath_h#canCall(_k#0, r#0)
         || (25 != $FunctionContextHeight
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> true);

function _module.__default.InfinitePath_h#requires(LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.InfinitePath_h
axiom (forall $ly: LayerType, _k#0: Box, r#0: DatatypeType :: 
  { _module.__default.InfinitePath_h#requires($ly, _k#0, r#0) } 
  $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
     ==> _module.__default.InfinitePath_h#requires($ly, _k#0, r#0) == true);

// definition axiom for _module.__default.InfinitePath_h (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, r#0: DatatypeType :: 
    { _module.__default.InfinitePath_h($LS($ly), _k#0, r#0) } 
    _module.__default.InfinitePath_h#canCall(_k#0, r#0)
         || (25 != $FunctionContextHeight
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.CoOption.None_q(r#0)
           ==> (var num#3 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
            _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), num#3)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.CoOption.None_q(r#0)
             then false
             else (var num#4 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.InfinitePath_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), num#4))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.InfinitePath_h($ly, _k'#0, r#0) } 
            ORD#Less(_k'#0, _k#0) ==> _module.__default.InfinitePath_h#canCall(_k'#0, r#0)))
         && _module.__default.InfinitePath_h($LS($ly), _k#0, r#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.CoOption.None_q(r#0)
                 then false
                 else (var num#2 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                  _module.__default.InfinitePath_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), num#2))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.InfinitePath_h($ly, _k'#0, r#0) } 
                ORD#Less(_k'#0, _k#0) ==> _module.__default.InfinitePath_h($ly, _k'#0, r#0)))));

// definition axiom for _module.__default.InfinitePath_h for decreasing-related literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, r#0: DatatypeType :: 
    {:weight 3} { _module.__default.InfinitePath_h($LS($ly), Lit(_k#0), r#0) } 
    _module.__default.InfinitePath_h#canCall(Lit(_k#0), r#0)
         || (25 != $FunctionContextHeight
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.CoOption.None_q(r#0)
           ==> (var num#6 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
            _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), num#6)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.CoOption.None_q(r#0)
             then false
             else (var num#7 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.InfinitePath_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), num#7))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.InfinitePath_h($LS($ly), _k'#1, r#0) } 
            ORD#Less(_k'#1, _k#0) ==> _module.__default.InfinitePath_h#canCall(_k'#1, r#0)))
         && _module.__default.InfinitePath_h($LS($ly), Lit(_k#0), r#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.CoOption.None_q(r#0)
                 then false
                 else (var num#5 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                  _module.__default.InfinitePath_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), num#5))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.InfinitePath_h($LS($ly), _k'#1, r#0) } 
                ORD#Less(_k'#1, _k#0) ==> _module.__default.InfinitePath_h($LS($ly), _k'#1, r#0)))));

// definition axiom for _module.__default.InfinitePath_h for all literals (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, r#0: DatatypeType :: 
    {:weight 3} { _module.__default.InfinitePath_h($LS($ly), Lit(_k#0), Lit(r#0)) } 
    _module.__default.InfinitePath_h#canCall(Lit(_k#0), Lit(r#0))
         || (25 != $FunctionContextHeight
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (0 < ORD#Offset(_k#0)
           ==> 
          !_module.CoOption.None_q(r#0)
           ==> (var num#9 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
            _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), num#9)))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.CoOption.None_q(r#0)
             then false
             else (var num#10 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.InfinitePath_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), num#10))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.InfinitePath_h($LS($ly), _k'#2, r#0) } 
            ORD#Less(_k'#2, _k#0) ==> _module.__default.InfinitePath_h#canCall(_k'#2, r#0)))
         && _module.__default.InfinitePath_h($LS($ly), Lit(_k#0), Lit(r#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.CoOption.None_q(r#0)
                 then false
                 else (var num#8 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                  _module.__default.InfinitePath_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), num#8))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.InfinitePath_h($LS($ly), _k'#2, r#0) } 
                ORD#Less(_k'#2, _k#0) ==> _module.__default.InfinitePath_h($LS($ly), _k'#2, r#0)))));

// function declaration for _module._default.InfinitePath'
function _module.__default.InfinitePath_k($ly: LayerType, num#0: DatatypeType) : bool;

function _module.__default.InfinitePath_k#canCall(num#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, num#0: DatatypeType :: 
  { _module.__default.InfinitePath_k($LS($ly), num#0) } 
  _module.__default.InfinitePath_k($LS($ly), num#0)
     == _module.__default.InfinitePath_k($ly, num#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, num#0: DatatypeType :: 
  { _module.__default.InfinitePath_k(AsFuelBottom($ly), num#0) } 
  _module.__default.InfinitePath_k($ly, num#0)
     == _module.__default.InfinitePath_k($LZ, num#0));

// consequence axiom for _module.__default.InfinitePath_k
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, num#0: DatatypeType :: 
    { _module.__default.InfinitePath_k($ly, num#0) } 
    _module.__default.InfinitePath_k#canCall(num#0)
         || (24 != $FunctionContextHeight && $Is(num#0, Tclass._module.Number()))
       ==> true);

function _module.__default.InfinitePath_k#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.InfinitePath_k
axiom (forall $ly: LayerType, num#0: DatatypeType :: 
  { _module.__default.InfinitePath_k#requires($ly, num#0) } 
  $Is(num#0, Tclass._module.Number())
     ==> _module.__default.InfinitePath_k#requires($ly, num#0) == true);

// definition axiom for _module.__default.InfinitePath_k (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, num#0: DatatypeType :: 
    { _module.__default.InfinitePath_k($LS($ly), num#0) } 
    _module.__default.InfinitePath_k#canCall(num#0)
         || (24 != $FunctionContextHeight && $Is(num#0, Tclass._module.Number()))
       ==> (_module.Number.Succ_q(num#0)
           ==> (var next#1 := _module.Number._h4(num#0); 
            _module.__default.InfinitePath_k#canCall(next#1)))
         && (!_module.Number.Succ_q(num#0)
           ==> (var r#1 := _module.Number._h5(num#0); 
            _module.__default.InfinitePath#canCall(r#1)))
         && _module.__default.InfinitePath_k($LS($ly), num#0)
           == (if _module.Number.Succ_q(num#0)
             then (var next#0 := _module.Number._h4(num#0); 
              _module.__default.InfinitePath_k($ly, next#0))
             else (var r#0 := _module.Number._h5(num#0); _module.__default.InfinitePath($ly, r#0))));

// 1st prefix predicate axiom for _module.__default.InfinitePath_k_h
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, num#0: DatatypeType :: 
    { _module.__default.InfinitePath_k($LS($ly), num#0) } 
    $Is(num#0, Tclass._module.Number())
         && _module.__default.InfinitePath_k($LS($ly), num#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.InfinitePath_k_h($LS($ly), _k#0, num#0) } 
        _module.__default.InfinitePath_k_h($LS($ly), _k#0, num#0)));

// 2nd prefix predicate axiom
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, num#0: DatatypeType :: 
    { _module.__default.InfinitePath_k($LS($ly), num#0) } 
    $Is(num#0, Tclass._module.Number())
         && (forall _k#0: Box :: 
          { _module.__default.InfinitePath_k_h($LS($ly), _k#0, num#0) } 
          _module.__default.InfinitePath_k_h($LS($ly), _k#0, num#0))
       ==> _module.__default.InfinitePath_k($LS($ly), num#0));

// 3rd prefix predicate axiom
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, num#0: DatatypeType, _k#0: Box :: 
    { _module.__default.InfinitePath_k_h($ly, _k#0, num#0) } 
    $Is(num#0, Tclass._module.Number()) && _k#0 == ORD#FromNat(0)
       ==> _module.__default.InfinitePath_k_h($ly, _k#0, num#0));

procedure CheckWellformed$$_module.__default.InfinitePath_k(num#0: DatatypeType where $Is(num#0, Tclass._module.Number()));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.InfinitePath_k(num#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#1#0: DatatypeType;
  var r#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##r#0: DatatypeType;
  var _mcc#0#0: DatatypeType;
  var next#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##num#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function InfinitePath'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(440,19): initial state"} true;
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
        if (num#0 == #_module.Number.Succ(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number());
            havoc next#Z#0;
            assume $Is(next#Z#0, Tclass._module.Number());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Number());
            assume next#Z#0 == let#1#0#0;
            ##num#0 := next#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.InfinitePath_k#canCall(next#Z#0);
            assume _module.__default.InfinitePath_k($LS($LZ), num#0)
               == _module.__default.InfinitePath_k($LS($LZ), next#Z#0);
            assume _module.__default.InfinitePath_k#canCall(next#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.InfinitePath_k($LS($LZ), num#0), TBool);
        }
        else if (num#0 == #_module.Number.Zero(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()));
            havoc r#Z#0;
            assume $Is(r#Z#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume r#Z#0 == let#0#0#0;
            ##r#0 := r#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.InfinitePath#canCall(r#Z#0);
            assume _module.__default.InfinitePath_k($LS($LZ), num#0)
               == _module.__default.InfinitePath($LS($LZ), r#Z#0);
            assume _module.__default.InfinitePath#canCall(r#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.InfinitePath_k($LS($LZ), num#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.InfinitePath'#
function _module.__default.InfinitePath_k_h($ly: LayerType, _k#0: Box, num#0: DatatypeType) : bool;

function _module.__default.InfinitePath_k_h#canCall(_k#0: Box, num#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, num#0: DatatypeType :: 
  { _module.__default.InfinitePath_k_h($LS($ly), _k#0, num#0) } 
  _module.__default.InfinitePath_k_h($LS($ly), _k#0, num#0)
     == _module.__default.InfinitePath_k_h($ly, _k#0, num#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, num#0: DatatypeType :: 
  { _module.__default.InfinitePath_k_h(AsFuelBottom($ly), _k#0, num#0) } 
  _module.__default.InfinitePath_k_h($ly, _k#0, num#0)
     == _module.__default.InfinitePath_k_h($LZ, _k#0, num#0));

// consequence axiom for _module.__default.InfinitePath_k_h
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, num#0: DatatypeType :: 
    { _module.__default.InfinitePath_k_h($ly, _k#0, num#0) } 
    _module.__default.InfinitePath_k_h#canCall(_k#0, num#0)
         || (26 != $FunctionContextHeight && $Is(num#0, Tclass._module.Number()))
       ==> true);

function _module.__default.InfinitePath_k_h#requires(LayerType, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.InfinitePath_k_h
axiom (forall $ly: LayerType, _k#0: Box, num#0: DatatypeType :: 
  { _module.__default.InfinitePath_k_h#requires($ly, _k#0, num#0) } 
  $Is(num#0, Tclass._module.Number())
     ==> _module.__default.InfinitePath_k_h#requires($ly, _k#0, num#0) == true);

// definition axiom for _module.__default.InfinitePath_k_h (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, num#0: DatatypeType :: 
    { _module.__default.InfinitePath_k_h($LS($ly), _k#0, num#0) } 
    _module.__default.InfinitePath_k_h#canCall(_k#0, num#0)
         || (26 != $FunctionContextHeight && $Is(num#0, Tclass._module.Number()))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Number.Succ_q(num#0)
               ==> (var next#3 := _module.Number._h4(num#0); 
                _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), next#3)))
             && (!_module.Number.Succ_q(num#0)
               ==> (var r#3 := _module.Number._h5(num#0); 
                _module.__default.InfinitePath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), r#3))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Number.Succ_q(num#0)
             then (var next#4 := _module.Number._h4(num#0); 
              _module.__default.InfinitePath_k_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), next#4))
             else (var r#4 := _module.Number._h5(num#0); 
              _module.__default.InfinitePath_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), r#4))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.InfinitePath_k_h($ly, _k'#0, num#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.InfinitePath_k_h#canCall(_k'#0, num#0)))
         && _module.__default.InfinitePath_k_h($LS($ly), _k#0, num#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Number.Succ_q(num#0)
                 then (var next#2 := _module.Number._h4(num#0); 
                  _module.__default.InfinitePath_k_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), next#2))
                 else (var r#2 := _module.Number._h5(num#0); 
                  _module.__default.InfinitePath_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), r#2))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.InfinitePath_k_h($ly, _k'#0, num#0) } 
                ORD#Less(_k'#0, _k#0) ==> _module.__default.InfinitePath_k_h($ly, _k'#0, num#0)))));

// definition axiom for _module.__default.InfinitePath_k_h for decreasing-related literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, num#0: DatatypeType :: 
    {:weight 3} { _module.__default.InfinitePath_k_h($LS($ly), Lit(_k#0), num#0) } 
    _module.__default.InfinitePath_k_h#canCall(Lit(_k#0), num#0)
         || (26 != $FunctionContextHeight && $Is(num#0, Tclass._module.Number()))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Number.Succ_q(num#0)
               ==> (var next#6 := _module.Number._h4(num#0); 
                _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), next#6)))
             && (!_module.Number.Succ_q(num#0)
               ==> (var r#6 := _module.Number._h5(num#0); 
                _module.__default.InfinitePath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), r#6))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Number.Succ_q(num#0)
             then (var next#7 := _module.Number._h4(num#0); 
              _module.__default.InfinitePath_k_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), next#7))
             else (var r#7 := _module.Number._h5(num#0); 
              _module.__default.InfinitePath_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), r#7))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.InfinitePath_k_h($LS($ly), _k'#1, num#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.InfinitePath_k_h#canCall(_k'#1, num#0)))
         && _module.__default.InfinitePath_k_h($LS($ly), Lit(_k#0), num#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Number.Succ_q(num#0)
                 then (var next#5 := _module.Number._h4(num#0); 
                  _module.__default.InfinitePath_k_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), next#5))
                 else (var r#5 := _module.Number._h5(num#0); 
                  _module.__default.InfinitePath_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), r#5))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.InfinitePath_k_h($LS($ly), _k'#1, num#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.InfinitePath_k_h($LS($ly), _k'#1, num#0)))));

// definition axiom for _module.__default.InfinitePath_k_h for all literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, num#0: DatatypeType :: 
    {:weight 3} { _module.__default.InfinitePath_k_h($LS($ly), Lit(_k#0), Lit(num#0)) } 
    _module.__default.InfinitePath_k_h#canCall(Lit(_k#0), Lit(num#0))
         || (26 != $FunctionContextHeight && $Is(num#0, Tclass._module.Number()))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Number.Succ_q(num#0)
               ==> (var next#9 := _module.Number._h4(num#0); 
                _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), next#9)))
             && (!_module.Number.Succ_q(num#0)
               ==> (var r#9 := _module.Number._h5(num#0); 
                _module.__default.InfinitePath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), r#9))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Number.Succ_q(num#0)
             then (var next#10 := _module.Number._h4(num#0); 
              _module.__default.InfinitePath_k_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), next#10))
             else (var r#10 := _module.Number._h5(num#0); 
              _module.__default.InfinitePath_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), r#10))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.InfinitePath_k_h($LS($ly), _k'#2, num#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.InfinitePath_k_h#canCall(_k'#2, num#0)))
         && _module.__default.InfinitePath_k_h($LS($ly), Lit(_k#0), Lit(num#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Number.Succ_q(num#0)
                 then (var next#8 := _module.Number._h4(num#0); 
                  _module.__default.InfinitePath_k_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), next#8))
                 else (var r#8 := _module.Number._h5(num#0); 
                  _module.__default.InfinitePath_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), r#8))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.InfinitePath_k_h($LS($ly), _k'#2, num#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.InfinitePath_k_h($LS($ly), _k'#2, num#0)))));

// function declaration for _module._default.ValidPath_Alt
function _module.__default.ValidPath__Alt($ly: LayerType, t#0: DatatypeType, r#0: DatatypeType) : bool;

function _module.__default.ValidPath__Alt#canCall(t#0: DatatypeType, r#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType, r#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt($LS($ly), t#0, r#0) } 
  _module.__default.ValidPath__Alt($LS($ly), t#0, r#0)
     == _module.__default.ValidPath__Alt($ly, t#0, r#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, t#0: DatatypeType, r#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt(AsFuelBottom($ly), t#0, r#0) } 
  _module.__default.ValidPath__Alt($ly, t#0, r#0)
     == _module.__default.ValidPath__Alt($LZ, t#0, r#0));

// consequence axiom for _module.__default.ValidPath__Alt
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, r#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt($ly, t#0, r#0) } 
    _module.__default.ValidPath__Alt#canCall(t#0, r#0)
         || (27 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> true);

function _module.__default.ValidPath__Alt#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ValidPath__Alt
axiom (forall $ly: LayerType, t#0: DatatypeType, r#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt#requires($ly, t#0, r#0) } 
  $Is(t#0, Tclass._module.Tree())
       && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
     ==> _module.__default.ValidPath__Alt#requires($ly, t#0, r#0) == true);

// definition axiom for _module.__default.ValidPath__Alt (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, r#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt($LS($ly), t#0, r#0) } 
    _module.__default.ValidPath__Alt#canCall(t#0, r#0)
         || (27 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (_module.CoOption.None_q(r#0) ==> $IsA#_module.Tree(t#0))
         && (!_module.CoOption.None_q(r#0)
           ==> (var num#1 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
            _module.Tree.Node_q(t#0)
               && _module.__default.ValidPath__Alt_k#canCall(_module.Tree.children(t#0), num#1)))
         && _module.__default.ValidPath__Alt($LS($ly), t#0, r#0)
           == (if _module.CoOption.None_q(r#0)
             then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
             else (var num#0 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.ValidPath__Alt_k($ly, _module.Tree.children(t#0), num#0))));

// 1st prefix predicate axiom for _module.__default.ValidPath__Alt_h
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, r#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt($LS($ly), t#0, r#0) } 
    $Is(t#0, Tclass._module.Tree())
         && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && _module.__default.ValidPath__Alt($LS($ly), t#0, r#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.ValidPath__Alt_h($LS($ly), _k#0, t#0, r#0) } 
        _module.__default.ValidPath__Alt_h($LS($ly), _k#0, t#0, r#0)));

// 2nd prefix predicate axiom
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, r#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt($LS($ly), t#0, r#0) } 
    $Is(t#0, Tclass._module.Tree())
         && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && (forall _k#0: Box :: 
          { _module.__default.ValidPath__Alt_h($LS($ly), _k#0, t#0, r#0) } 
          _module.__default.ValidPath__Alt_h($LS($ly), _k#0, t#0, r#0))
       ==> _module.__default.ValidPath__Alt($LS($ly), t#0, r#0));

// 3rd prefix predicate axiom
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, t#0: DatatypeType, r#0: DatatypeType, _k#0: Box :: 
    { _module.__default.ValidPath__Alt_h($ly, _k#0, t#0, r#0) } 
    $Is(t#0, Tclass._module.Tree())
         && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.ValidPath__Alt_h($ly, _k#0, t#0, r#0));

procedure CheckWellformed$$_module.__default.ValidPath__Alt(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()), 
    r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ValidPath__Alt(t#0: DatatypeType, r#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var num#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##num#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ValidPath_Alt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(450,19): initial state"} true;
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
        if (r#0 == #_module.CoOption.None())
        {
            assume _module.__default.ValidPath__Alt($LS($LZ), t#0, r#0)
               == _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())));
            assume $IsA#_module.Tree(t#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ValidPath__Alt($LS($LZ), t#0, r#0), TBool);
        }
        else if (r#0 == #_module.CoOption.Some($Box(_mcc#0#0)))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number());
            havoc num#Z#0;
            assume $Is(num#Z#0, Tclass._module.Number());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Number());
            assume num#Z#0 == let#0#0#0;
            assume _module.Tree.Node_q(t#0);
            ##s#0 := _module.Tree.children(t#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##num#0 := num#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.ValidPath__Alt_k#canCall(_module.Tree.children(t#0), num#Z#0);
            assume _module.__default.ValidPath__Alt($LS($LZ), t#0, r#0)
               == _module.__default.ValidPath__Alt_k($LS($LZ), _module.Tree.children(t#0), num#Z#0);
            assume _module.Tree.Node_q(t#0)
               && _module.__default.ValidPath__Alt_k#canCall(_module.Tree.children(t#0), num#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ValidPath__Alt($LS($LZ), t#0, r#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.ValidPath_Alt#
function _module.__default.ValidPath__Alt_h($ly: LayerType, _k#0: Box, t#0: DatatypeType, r#0: DatatypeType) : bool;

function _module.__default.ValidPath__Alt_h#canCall(_k#0: Box, t#0: DatatypeType, r#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, r#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_h($LS($ly), _k#0, t#0, r#0) } 
  _module.__default.ValidPath__Alt_h($LS($ly), _k#0, t#0, r#0)
     == _module.__default.ValidPath__Alt_h($ly, _k#0, t#0, r#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, r#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_h(AsFuelBottom($ly), _k#0, t#0, r#0) } 
  _module.__default.ValidPath__Alt_h($ly, _k#0, t#0, r#0)
     == _module.__default.ValidPath__Alt_h($LZ, _k#0, t#0, r#0));

// consequence axiom for _module.__default.ValidPath__Alt_h
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, r#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt_h($ly, _k#0, t#0, r#0) } 
    _module.__default.ValidPath__Alt_h#canCall(_k#0, t#0, r#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> true);

function _module.__default.ValidPath__Alt_h#requires(LayerType, Box, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ValidPath__Alt_h
axiom (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, r#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_h#requires($ly, _k#0, t#0, r#0) } 
  $Is(t#0, Tclass._module.Tree())
       && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
     ==> _module.__default.ValidPath__Alt_h#requires($ly, _k#0, t#0, r#0) == true);

// definition axiom for _module.__default.ValidPath__Alt_h (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, r#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt_h($LS($ly), _k#0, t#0, r#0) } 
    _module.__default.ValidPath__Alt_h#canCall(_k#0, t#0, r#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.CoOption.None_q(r#0) ==> $IsA#_module.Tree(t#0))
             && (!_module.CoOption.None_q(r#0)
               ==> (var num#3 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                _module.Tree.Node_q(t#0)
                   && _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#3))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.CoOption.None_q(r#0)
             then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
             else (var num#4 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.ValidPath__Alt_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#4))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.ValidPath__Alt_h($ly, _k'#0, t#0, r#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.ValidPath__Alt_h#canCall(_k'#0, t#0, r#0)))
         && _module.__default.ValidPath__Alt_h($LS($ly), _k#0, t#0, r#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.CoOption.None_q(r#0)
                 then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
                 else (var num#2 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                  _module.__default.ValidPath__Alt_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#2))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.ValidPath__Alt_h($ly, _k'#0, t#0, r#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.ValidPath__Alt_h($ly, _k'#0, t#0, r#0)))));

// definition axiom for _module.__default.ValidPath__Alt_h for decreasing-related literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, r#0: DatatypeType :: 
    {:weight 3} { _module.__default.ValidPath__Alt_h($LS($ly), Lit(_k#0), t#0, r#0) } 
    _module.__default.ValidPath__Alt_h#canCall(Lit(_k#0), t#0, r#0)
         || (28 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.CoOption.None_q(r#0) ==> $IsA#_module.Tree(t#0))
             && (!_module.CoOption.None_q(r#0)
               ==> (var num#6 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                _module.Tree.Node_q(t#0)
                   && _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#6))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.CoOption.None_q(r#0)
             then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
             else (var num#7 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.ValidPath__Alt_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#7))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.ValidPath__Alt_h($LS($ly), _k'#1, t#0, r#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.ValidPath__Alt_h#canCall(_k'#1, t#0, r#0)))
         && _module.__default.ValidPath__Alt_h($LS($ly), Lit(_k#0), t#0, r#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.CoOption.None_q(r#0)
                 then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
                 else (var num#5 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                  _module.__default.ValidPath__Alt_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#5))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.ValidPath__Alt_h($LS($ly), _k'#1, t#0, r#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.ValidPath__Alt_h($LS($ly), _k'#1, t#0, r#0)))));

// definition axiom for _module.__default.ValidPath__Alt_h for all literals (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, t#0: DatatypeType, r#0: DatatypeType :: 
    {:weight 3} { _module.__default.ValidPath__Alt_h($LS($ly), Lit(_k#0), Lit(t#0), Lit(r#0)) } 
    _module.__default.ValidPath__Alt_h#canCall(Lit(_k#0), Lit(t#0), Lit(r#0))
         || (28 != $FunctionContextHeight
           && 
          $Is(t#0, Tclass._module.Tree())
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.CoOption.None_q(r#0) ==> $IsA#_module.Tree(t#0))
             && (!_module.CoOption.None_q(r#0)
               ==> (var num#9 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                _module.Tree.Node_q(t#0)
                   && _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#9))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.CoOption.None_q(r#0)
             then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
             else (var num#10 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.ValidPath__Alt_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#10))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.ValidPath__Alt_h($LS($ly), _k'#2, t#0, r#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.ValidPath__Alt_h#canCall(_k'#2, t#0, r#0)))
         && _module.__default.ValidPath__Alt_h($LS($ly), Lit(_k#0), Lit(t#0), Lit(r#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.CoOption.None_q(r#0)
                 then _module.Tree#Equal(t#0, #_module.Tree.Node(Lit(#_module.Stream.Nil())))
                 else (var num#8 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
                  _module.__default.ValidPath__Alt_k_h($LS($LZ), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Tree.children(t#0), num#8))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.ValidPath__Alt_h($LS($ly), _k'#2, t#0, r#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.ValidPath__Alt_h($LS($ly), _k'#2, t#0, r#0)))));

// function declaration for _module._default.ValidPath_Alt'
function _module.__default.ValidPath__Alt_k($ly: LayerType, s#0: DatatypeType, num#0: DatatypeType) : bool;

function _module.__default.ValidPath__Alt_k#canCall(s#0: DatatypeType, num#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType, num#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_k($LS($ly), s#0, num#0) } 
  _module.__default.ValidPath__Alt_k($LS($ly), s#0, num#0)
     == _module.__default.ValidPath__Alt_k($ly, s#0, num#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, s#0: DatatypeType, num#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_k(AsFuelBottom($ly), s#0, num#0) } 
  _module.__default.ValidPath__Alt_k($ly, s#0, num#0)
     == _module.__default.ValidPath__Alt_k($LZ, s#0, num#0));

// consequence axiom for _module.__default.ValidPath__Alt_k
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, num#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt_k($ly, s#0, num#0) } 
    _module.__default.ValidPath__Alt_k#canCall(s#0, num#0)
         || (27 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && $Is(num#0, Tclass._module.Number()))
       ==> true);

function _module.__default.ValidPath__Alt_k#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ValidPath__Alt_k
axiom (forall $ly: LayerType, s#0: DatatypeType, num#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_k#requires($ly, s#0, num#0) } 
  $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
       && $Is(num#0, Tclass._module.Number())
     ==> _module.__default.ValidPath__Alt_k#requires($ly, s#0, num#0) == true);

// definition axiom for _module.__default.ValidPath__Alt_k (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, num#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt_k($LS($ly), s#0, num#0) } 
    _module.__default.ValidPath__Alt_k#canCall(s#0, num#0)
         || (27 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && $Is(num#0, Tclass._module.Number()))
       ==> (_module.Number.Succ_q(num#0)
           ==> (var next#1 := _module.Number._h4(num#0); 
            _module.Stream.Cons_q(s#0)
               ==> _module.__default.ValidPath__Alt_k#canCall(_module.Stream.tail(s#0), next#1)))
         && (!_module.Number.Succ_q(num#0)
           ==> (var r#1 := _module.Number._h5(num#0); 
            _module.Stream.Cons_q(s#0)
               ==> _module.__default.ValidPath__Alt#canCall($Unbox(_module.Stream.head(s#0)): DatatypeType, r#1)))
         && _module.__default.ValidPath__Alt_k($LS($ly), s#0, num#0)
           == (if _module.Number.Succ_q(num#0)
             then (var next#0 := _module.Number._h4(num#0); 
              _module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt_k($ly, _module.Stream.tail(s#0), next#0))
             else (var r#0 := _module.Number._h5(num#0); 
              _module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt($ly, $Unbox(_module.Stream.head(s#0)): DatatypeType, r#0))));

// 1st prefix predicate axiom for _module.__default.ValidPath__Alt_k_h
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, num#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt_k($LS($ly), s#0, num#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $Is(num#0, Tclass._module.Number())
         && _module.__default.ValidPath__Alt_k($LS($ly), s#0, num#0)
       ==> (forall _k#0: Box :: 
        { _module.__default.ValidPath__Alt_k_h($LS($ly), _k#0, s#0, num#0) } 
        _module.__default.ValidPath__Alt_k_h($LS($ly), _k#0, s#0, num#0)));

// 2nd prefix predicate axiom
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, num#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt_k($LS($ly), s#0, num#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $Is(num#0, Tclass._module.Number())
         && (forall _k#0: Box :: 
          { _module.__default.ValidPath__Alt_k_h($LS($ly), _k#0, s#0, num#0) } 
          _module.__default.ValidPath__Alt_k_h($LS($ly), _k#0, s#0, num#0))
       ==> _module.__default.ValidPath__Alt_k($LS($ly), s#0, num#0));

// 3rd prefix predicate axiom
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, s#0: DatatypeType, num#0: DatatypeType, _k#0: Box :: 
    { _module.__default.ValidPath__Alt_k_h($ly, _k#0, s#0, num#0) } 
    $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $Is(num#0, Tclass._module.Number())
         && _k#0 == ORD#FromNat(0)
       ==> _module.__default.ValidPath__Alt_k_h($ly, _k#0, s#0, num#0));

procedure CheckWellformed$$_module.__default.ValidPath__Alt_k(s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree())), 
    num#0: DatatypeType where $Is(num#0, Tclass._module.Number()));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ValidPath__Alt_k(s#0: DatatypeType, num#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#1#0: DatatypeType;
  var r#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##t#0: DatatypeType;
  var ##r#0: DatatypeType;
  var _mcc#0#0: DatatypeType;
  var next#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##num#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ValidPath_Alt'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(456,19): initial state"} true;
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
        if (num#0 == #_module.Number.Succ(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number());
            havoc next#Z#0;
            assume $Is(next#Z#0, Tclass._module.Number());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Number());
            assume next#Z#0 == let#1#0#0;
            if (_module.Stream.Cons_q(s#0))
            {
                assert _module.Stream.Cons_q(s#0);
                ##s#0 := _module.Stream.tail(s#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##num#0 := next#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.ValidPath__Alt_k#canCall(_module.Stream.tail(s#0), next#Z#0);
            }

            assume _module.__default.ValidPath__Alt_k($LS($LZ), s#0, num#0)
               == (_module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt_k($LS($LZ), _module.Stream.tail(s#0), next#Z#0));
            assume _module.Stream.Cons_q(s#0)
               ==> _module.__default.ValidPath__Alt_k#canCall(_module.Stream.tail(s#0), next#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ValidPath__Alt_k($LS($LZ), s#0, num#0), TBool);
        }
        else if (num#0 == #_module.Number.Zero(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()));
            havoc r#Z#0;
            assume $Is(r#Z#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume r#Z#0 == let#0#0#0;
            if (_module.Stream.Cons_q(s#0))
            {
                assert _module.Stream.Cons_q(s#0);
                ##t#0 := $Unbox(_module.Stream.head(s#0)): DatatypeType;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
                ##r#0 := r#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.ValidPath__Alt#canCall($Unbox(_module.Stream.head(s#0)): DatatypeType, r#Z#0);
            }

            assume _module.__default.ValidPath__Alt_k($LS($LZ), s#0, num#0)
               == (_module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt($LS($LZ), $Unbox(_module.Stream.head(s#0)): DatatypeType, r#Z#0));
            assume _module.Stream.Cons_q(s#0)
               ==> _module.__default.ValidPath__Alt#canCall($Unbox(_module.Stream.head(s#0)): DatatypeType, r#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.ValidPath__Alt_k($LS($LZ), s#0, num#0), TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.ValidPath_Alt'#
function _module.__default.ValidPath__Alt_k_h($ly: LayerType, _k#0: Box, s#0: DatatypeType, num#0: DatatypeType) : bool;

function _module.__default.ValidPath__Alt_k_h#canCall(_k#0: Box, s#0: DatatypeType, num#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, num#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_k_h($LS($ly), _k#0, s#0, num#0) } 
  _module.__default.ValidPath__Alt_k_h($LS($ly), _k#0, s#0, num#0)
     == _module.__default.ValidPath__Alt_k_h($ly, _k#0, s#0, num#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, num#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_k_h(AsFuelBottom($ly), _k#0, s#0, num#0) } 
  _module.__default.ValidPath__Alt_k_h($ly, _k#0, s#0, num#0)
     == _module.__default.ValidPath__Alt_k_h($LZ, _k#0, s#0, num#0));

// consequence axiom for _module.__default.ValidPath__Alt_k_h
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, num#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt_k_h($ly, _k#0, s#0, num#0) } 
    _module.__default.ValidPath__Alt_k_h#canCall(_k#0, s#0, num#0)
         || (29 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && $Is(num#0, Tclass._module.Number()))
       ==> true);

function _module.__default.ValidPath__Alt_k_h#requires(LayerType, Box, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.ValidPath__Alt_k_h
axiom (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, num#0: DatatypeType :: 
  { _module.__default.ValidPath__Alt_k_h#requires($ly, _k#0, s#0, num#0) } 
  $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
       && $Is(num#0, Tclass._module.Number())
     ==> _module.__default.ValidPath__Alt_k_h#requires($ly, _k#0, s#0, num#0) == true);

// definition axiom for _module.__default.ValidPath__Alt_k_h (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, num#0: DatatypeType :: 
    { _module.__default.ValidPath__Alt_k_h($LS($ly), _k#0, s#0, num#0) } 
    _module.__default.ValidPath__Alt_k_h#canCall(_k#0, s#0, num#0)
         || (29 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && $Is(num#0, Tclass._module.Number()))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Number.Succ_q(num#0)
               ==> (var next#3 := _module.Number._h4(num#0); 
                _module.Stream.Cons_q(s#0)
                   ==> _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#3)))
             && (!_module.Number.Succ_q(num#0)
               ==> (var r#3 := _module.Number._h5(num#0); 
                _module.Stream.Cons_q(s#0)
                   ==> _module.__default.ValidPath__Alt_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                    r#3))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Number.Succ_q(num#0)
             then (var next#4 := _module.Number._h4(num#0); 
              _module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt_k_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#4))
             else (var r#4 := _module.Number._h5(num#0); 
              _module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                  r#4))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#0: Box :: 
            { _module.__default.ValidPath__Alt_k_h($ly, _k'#0, s#0, num#0) } 
            ORD#Less(_k'#0, _k#0)
               ==> _module.__default.ValidPath__Alt_k_h#canCall(_k'#0, s#0, num#0)))
         && _module.__default.ValidPath__Alt_k_h($LS($ly), _k#0, s#0, num#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Number.Succ_q(num#0)
                 then (var next#2 := _module.Number._h4(num#0); 
                  _module.Stream.Cons_q(s#0)
                     && _module.__default.ValidPath__Alt_k_h($ly, ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#2))
                 else (var r#2 := _module.Number._h5(num#0); 
                  _module.Stream.Cons_q(s#0)
                     && _module.__default.ValidPath__Alt_h($LS($LZ), 
                      ORD#Minus(_k#0, ORD#FromNat(1)), 
                      $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                      r#2))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#0: Box :: 
                { _module.__default.ValidPath__Alt_k_h($ly, _k'#0, s#0, num#0) } 
                ORD#Less(_k'#0, _k#0)
                   ==> _module.__default.ValidPath__Alt_k_h($ly, _k'#0, s#0, num#0)))));

// definition axiom for _module.__default.ValidPath__Alt_k_h for decreasing-related literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, num#0: DatatypeType :: 
    {:weight 3} { _module.__default.ValidPath__Alt_k_h($LS($ly), Lit(_k#0), s#0, num#0) } 
    _module.__default.ValidPath__Alt_k_h#canCall(Lit(_k#0), s#0, num#0)
         || (29 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && $Is(num#0, Tclass._module.Number()))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Number.Succ_q(num#0)
               ==> (var next#6 := _module.Number._h4(num#0); 
                _module.Stream.Cons_q(s#0)
                   ==> _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#6)))
             && (!_module.Number.Succ_q(num#0)
               ==> (var r#6 := _module.Number._h5(num#0); 
                _module.Stream.Cons_q(s#0)
                   ==> _module.__default.ValidPath__Alt_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                    r#6))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Number.Succ_q(num#0)
             then (var next#7 := _module.Number._h4(num#0); 
              _module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt_k_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#7))
             else (var r#7 := _module.Number._h5(num#0); 
              _module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                  r#7))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#1: Box :: 
            { _module.__default.ValidPath__Alt_k_h($LS($ly), _k'#1, s#0, num#0) } 
            ORD#Less(_k'#1, _k#0)
               ==> _module.__default.ValidPath__Alt_k_h#canCall(_k'#1, s#0, num#0)))
         && _module.__default.ValidPath__Alt_k_h($LS($ly), Lit(_k#0), s#0, num#0)
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Number.Succ_q(num#0)
                 then (var next#5 := _module.Number._h4(num#0); 
                  _module.Stream.Cons_q(s#0)
                     && _module.__default.ValidPath__Alt_k_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#5))
                 else (var r#5 := _module.Number._h5(num#0); 
                  _module.Stream.Cons_q(s#0)
                     && _module.__default.ValidPath__Alt_h($LS($LZ), 
                      ORD#Minus(_k#0, ORD#FromNat(1)), 
                      $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                      r#5))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#1: Box :: 
                { _module.__default.ValidPath__Alt_k_h($LS($ly), _k'#1, s#0, num#0) } 
                ORD#Less(_k'#1, _k#0)
                   ==> _module.__default.ValidPath__Alt_k_h($LS($ly), _k'#1, s#0, num#0)))));

// definition axiom for _module.__default.ValidPath__Alt_k_h for all literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, _k#0: Box, s#0: DatatypeType, num#0: DatatypeType :: 
    {:weight 3} { _module.__default.ValidPath__Alt_k_h($LS($ly), Lit(_k#0), Lit(s#0), Lit(num#0)) } 
    _module.__default.ValidPath__Alt_k_h#canCall(Lit(_k#0), Lit(s#0), Lit(num#0))
         || (29 != $FunctionContextHeight
           && 
          $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
           && $Is(num#0, Tclass._module.Number()))
       ==> (0 < ORD#Offset(_k#0)
           ==> (_module.Number.Succ_q(num#0)
               ==> (var next#9 := _module.Number._h4(num#0); 
                _module.Stream.Cons_q(s#0)
                   ==> _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#9)))
             && (!_module.Number.Succ_q(num#0)
               ==> (var r#9 := _module.Number._h5(num#0); 
                _module.Stream.Cons_q(s#0)
                   ==> _module.__default.ValidPath__Alt_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                    r#9))))
         && (
          (0 < ORD#Offset(_k#0)
           ==> (if _module.Number.Succ_q(num#0)
             then (var next#10 := _module.Number._h4(num#0); 
              _module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt_k_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#10))
             else (var r#10 := _module.Number._h5(num#0); 
              _module.Stream.Cons_q(s#0)
                 && _module.__default.ValidPath__Alt_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                  r#10))))
           ==> 
          LitInt(0) == ORD#Offset(_k#0)
           ==> (forall _k'#2: Box :: 
            { _module.__default.ValidPath__Alt_k_h($LS($ly), _k'#2, s#0, num#0) } 
            ORD#Less(_k'#2, _k#0)
               ==> _module.__default.ValidPath__Alt_k_h#canCall(_k'#2, s#0, num#0)))
         && _module.__default.ValidPath__Alt_k_h($LS($ly), Lit(_k#0), Lit(s#0), Lit(num#0))
           == ((0 < ORD#Offset(_k#0)
               ==> (if _module.Number.Succ_q(num#0)
                 then (var next#8 := _module.Number._h4(num#0); 
                  _module.Stream.Cons_q(s#0)
                     && _module.__default.ValidPath__Alt_k_h($LS($ly), ORD#Minus(_k#0, ORD#FromNat(1)), _module.Stream.tail(s#0), next#8))
                 else (var r#8 := _module.Number._h5(num#0); 
                  _module.Stream.Cons_q(s#0)
                     && _module.__default.ValidPath__Alt_h($LS($LZ), 
                      ORD#Minus(_k#0, ORD#FromNat(1)), 
                      $Unbox(_module.Stream.head(s#0)): DatatypeType, 
                      r#8))))
             && (LitInt(0) == ORD#Offset(_k#0)
               ==> (forall _k'#2: Box :: 
                { _module.__default.ValidPath__Alt_k_h($LS($ly), _k'#2, s#0, num#0) } 
                ORD#Less(_k'#2, _k#0)
                   ==> _module.__default.ValidPath__Alt_k_h($LS($ly), _k'#2, s#0, num#0)))));

// function declaration for _module._default.HasFiniteHeight_Alt
function _module.__default.HasFiniteHeight__Alt(t#0: DatatypeType) : bool;

function _module.__default.HasFiniteHeight__Alt#canCall(t#0: DatatypeType) : bool;

// consequence axiom for _module.__default.HasFiniteHeight__Alt
axiom 60 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.HasFiniteHeight__Alt(t#0) } 
    _module.__default.HasFiniteHeight__Alt#canCall(t#0)
         || (60 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> true);

function _module.__default.HasFiniteHeight__Alt#requires(DatatypeType) : bool;

// #requires axiom for _module.__default.HasFiniteHeight__Alt
axiom (forall t#0: DatatypeType :: 
  { _module.__default.HasFiniteHeight__Alt#requires(t#0) } 
  $Is(t#0, Tclass._module.Tree())
     ==> _module.__default.HasFiniteHeight__Alt#requires(t#0) == true);

// definition axiom for _module.__default.HasFiniteHeight__Alt (revealed)
axiom 60 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    { _module.__default.HasFiniteHeight__Alt(t#0) } 
    _module.__default.HasFiniteHeight__Alt#canCall(t#0)
         || (60 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (forall r#0: DatatypeType :: 
          { _module.__default.InfinitePath($LS($LZ), r#0) } 
            { _module.__default.ValidPath__Alt($LS($LZ), t#0, r#0) } 
          $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
             ==> _module.__default.ValidPath__Alt#canCall(t#0, r#0)
               && (_module.__default.ValidPath__Alt($LS($LZ), t#0, r#0)
                 ==> _module.__default.InfinitePath#canCall(r#0)))
         && _module.__default.HasFiniteHeight__Alt(t#0)
           == (forall r#0: DatatypeType :: 
            { _module.__default.InfinitePath($LS($LZ), r#0) } 
              { _module.__default.ValidPath__Alt($LS($LZ), t#0, r#0) } 
            $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
               ==> 
              _module.__default.ValidPath__Alt($LS($LZ), t#0, r#0)
               ==> !_module.__default.InfinitePath($LS($LZ), r#0)));

// definition axiom for _module.__default.HasFiniteHeight__Alt for all literals (revealed)
axiom 60 <= $FunctionContextHeight
   ==> (forall t#0: DatatypeType :: 
    {:weight 3} { _module.__default.HasFiniteHeight__Alt(Lit(t#0)) } 
    _module.__default.HasFiniteHeight__Alt#canCall(Lit(t#0))
         || (60 != $FunctionContextHeight && $Is(t#0, Tclass._module.Tree()))
       ==> (forall r#1: DatatypeType :: 
          { _module.__default.InfinitePath($LS($LZ), r#1) } 
            { _module.__default.ValidPath__Alt($LS($LZ), t#0, r#1) } 
          $Is(r#1, Tclass._module.CoOption(Tclass._module.Number()))
             ==> _module.__default.ValidPath__Alt#canCall(Lit(t#0), r#1)
               && (_module.__default.ValidPath__Alt($LS($LZ), Lit(t#0), r#1)
                 ==> _module.__default.InfinitePath#canCall(r#1)))
         && _module.__default.HasFiniteHeight__Alt(Lit(t#0))
           == (forall r#1: DatatypeType :: 
            { _module.__default.InfinitePath($LS($LZ), r#1) } 
              { _module.__default.ValidPath__Alt($LS($LZ), t#0, r#1) } 
            $Is(r#1, Tclass._module.CoOption(Tclass._module.Number()))
               ==> 
              _module.__default.ValidPath__Alt($LS($LZ), Lit(t#0), r#1)
               ==> !_module.__default.InfinitePath($LS($LZ), r#1)));

procedure CheckWellformed$$_module.__default.HasFiniteHeight__Alt(t#0: DatatypeType where $Is(t#0, Tclass._module.Tree()));
  free requires 60 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.HasFiniteHeight__Alt(t#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var r#2: DatatypeType;
  var ##t#0: DatatypeType;
  var ##r#0: DatatypeType;
  var ##r#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function HasFiniteHeight_Alt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(466,10): initial state"} true;
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
        // Begin Comprehension WF check
        havoc r#2;
        if ($Is(r#2, Tclass._module.CoOption(Tclass._module.Number())))
        {
            ##t#0 := t#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
            ##r#0 := r#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.ValidPath__Alt#canCall(t#0, r#2);
            if (_module.__default.ValidPath__Alt($LS($LZ), t#0, r#2))
            {
                ##r#1 := r#2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.InfinitePath#canCall(r#2);
            }
        }

        // End Comprehension WF check
        assume _module.__default.HasFiniteHeight__Alt(t#0)
           == (forall r#3: DatatypeType :: 
            { _module.__default.InfinitePath($LS($LZ), r#3) } 
              { _module.__default.ValidPath__Alt($LS($LZ), t#0, r#3) } 
            $Is(r#3, Tclass._module.CoOption(Tclass._module.Number()))
               ==> 
              _module.__default.ValidPath__Alt($LS($LZ), t#0, r#3)
               ==> !_module.__default.InfinitePath($LS($LZ), r#3));
        assume (forall r#3: DatatypeType :: 
          { _module.__default.InfinitePath($LS($LZ), r#3) } 
            { _module.__default.ValidPath__Alt($LS($LZ), t#0, r#3) } 
          $Is(r#3, Tclass._module.CoOption(Tclass._module.Number()))
             ==> _module.__default.ValidPath__Alt#canCall(t#0, r#3)
               && (_module.__default.ValidPath__Alt($LS($LZ), t#0, r#3)
                 ==> _module.__default.InfinitePath#canCall(r#3)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.HasFiniteHeight__Alt(t#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.S2N
function _module.__default.S2N($ly: LayerType, p#0: DatatypeType) : DatatypeType;

function _module.__default.S2N#canCall(p#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, p#0: DatatypeType :: 
  { _module.__default.S2N($LS($ly), p#0) } 
  _module.__default.S2N($LS($ly), p#0) == _module.__default.S2N($ly, p#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, p#0: DatatypeType :: 
  { _module.__default.S2N(AsFuelBottom($ly), p#0) } 
  _module.__default.S2N($ly, p#0) == _module.__default.S2N($LZ, p#0));

// consequence axiom for _module.__default.S2N
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, p#0: DatatypeType :: 
    { _module.__default.S2N($ly, p#0) } 
    _module.__default.S2N#canCall(p#0)
         || (30 != $FunctionContextHeight && $Is(p#0, Tclass._module.Stream(TInt)))
       ==> $Is(_module.__default.S2N($ly, p#0), 
        Tclass._module.CoOption(Tclass._module.Number())));

function _module.__default.S2N#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.S2N
axiom (forall $ly: LayerType, p#0: DatatypeType :: 
  { _module.__default.S2N#requires($ly, p#0) } 
  $Is(p#0, Tclass._module.Stream(TInt))
     ==> _module.__default.S2N#requires($ly, p#0) == true);

// definition axiom for _module.__default.S2N (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, p#0: DatatypeType :: 
    { _module.__default.S2N($LS($ly), p#0) } 
    _module.__default.S2N#canCall(p#0)
         || (30 != $FunctionContextHeight && $Is(p#0, Tclass._module.Stream(TInt)))
       ==> (!_module.Stream.Nil_q(p#0)
           ==> (var tail#1 := _module.Stream.tail(p#0); 
            (var n#1 := $Unbox(_module.Stream.head(p#0)): int; 
              _module.__default.S2N_k#canCall((if n#1 < 0 then 0 else n#1), tail#1))))
         && _module.__default.S2N($LS($ly), p#0)
           == (if _module.Stream.Nil_q(p#0)
             then #_module.CoOption.None()
             else (var tail#0 := _module.Stream.tail(p#0); 
              (var n#0 := $Unbox(_module.Stream.head(p#0)): int; 
                #_module.CoOption.Some($Box(_module.__default.S2N_k($ly, (if n#0 < 0 then 0 else n#0), tail#0)))))));

procedure CheckWellformed$$_module.__default.S2N(p#0: DatatypeType where $Is(p#0, Tclass._module.Stream(TInt)));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.S2N(p#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var n#Z#0: int;
  var let#1#0#0: int;
  var ##n#0: int;
  var ##tail#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function S2N
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(475,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.S2N($LS($LZ), p#0), 
          Tclass._module.CoOption(Tclass._module.Number()));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (p#0 == #_module.Stream.Nil())
        {
            assume _module.__default.S2N($LS($LZ), p#0) == Lit(#_module.CoOption.None());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.S2N($LS($LZ), p#0), 
              Tclass._module.CoOption(Tclass._module.Number()));
        }
        else if (p#0 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.Stream(TInt));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.Stream(TInt));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Stream(TInt));
            assume tail#Z#0 == let#0#0#0;
            havoc n#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume n#Z#0 == let#1#0#0;
            if (n#Z#0 < 0)
            {
            }
            else
            {
            }

            assert $Is((if n#Z#0 < 0 then 0 else n#Z#0), Tclass._System.nat());
            ##n#0 := (if n#Z#0 < 0 then 0 else n#Z#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##tail#0 := tail#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##tail#0, Tclass._module.Stream(TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.S2N_k#canCall((if n#Z#0 < 0 then 0 else n#Z#0), tail#Z#0);
            assume _module.__default.S2N($LS($LZ), p#0)
               == #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#Z#0 < 0 then 0 else n#Z#0), tail#Z#0)));
            assume _module.__default.S2N_k#canCall((if n#Z#0 < 0 then 0 else n#Z#0), tail#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.S2N($LS($LZ), p#0), 
              Tclass._module.CoOption(Tclass._module.Number()));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.S2N'
function _module.__default.S2N_k($ly: LayerType, n#0: int, tail#0: DatatypeType) : DatatypeType;

function _module.__default.S2N_k#canCall(n#0: int, tail#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int, tail#0: DatatypeType :: 
  { _module.__default.S2N_k($LS($ly), n#0, tail#0) } 
  _module.__default.S2N_k($LS($ly), n#0, tail#0)
     == _module.__default.S2N_k($ly, n#0, tail#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int, tail#0: DatatypeType :: 
  { _module.__default.S2N_k(AsFuelBottom($ly), n#0, tail#0) } 
  _module.__default.S2N_k($ly, n#0, tail#0)
     == _module.__default.S2N_k($LZ, n#0, tail#0));

// consequence axiom for _module.__default.S2N_k
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int, tail#0: DatatypeType :: 
    { _module.__default.S2N_k($ly, n#0, tail#0) } 
    _module.__default.S2N_k#canCall(n#0, tail#0)
         || (30 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(tail#0, Tclass._module.Stream(TInt)))
       ==> $Is(_module.__default.S2N_k($ly, n#0, tail#0), Tclass._module.Number()));

function _module.__default.S2N_k#requires(LayerType, int, DatatypeType) : bool;

// #requires axiom for _module.__default.S2N_k
axiom (forall $ly: LayerType, n#0: int, tail#0: DatatypeType :: 
  { _module.__default.S2N_k#requires($ly, n#0, tail#0) } 
  LitInt(0) <= n#0 && $Is(tail#0, Tclass._module.Stream(TInt))
     ==> _module.__default.S2N_k#requires($ly, n#0, tail#0) == true);

// definition axiom for _module.__default.S2N_k (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int, tail#0: DatatypeType :: 
    { _module.__default.S2N_k($LS($ly), n#0, tail#0) } 
    _module.__default.S2N_k#canCall(n#0, tail#0)
         || (30 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(tail#0, Tclass._module.Stream(TInt)))
       ==> (n#0 <= LitInt(0) ==> _module.__default.S2N#canCall(tail#0))
         && (LitInt(0) < n#0 ==> _module.__default.S2N_k#canCall(n#0 - 1, tail#0))
         && _module.__default.S2N_k($LS($ly), n#0, tail#0)
           == (if n#0 <= LitInt(0)
             then #_module.Number.Zero(_module.__default.S2N($ly, tail#0))
             else #_module.Number.Succ(_module.__default.S2N_k($ly, n#0 - 1, tail#0))));

procedure CheckWellformed$$_module.__default.S2N_k(n#0: int where LitInt(0) <= n#0, 
    tail#0: DatatypeType where $Is(tail#0, Tclass._module.Stream(TInt)));
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.S2N_k(n#0: int, tail#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##p#0: DatatypeType;
  var ##n#0: int;
  var ##tail#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function S2N'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(482,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.S2N_k($LS($LZ), n#0, tail#0), Tclass._module.Number());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 <= LitInt(0))
        {
            ##p#0 := tail#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##p#0, Tclass._module.Stream(TInt), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= LitInt(1) || LitInt(0) == LitInt(1);
            assert 0 <= n#0 + 1 || LitInt(0) < LitInt(1) || LitInt(0) == n#0 + 1;
            assert LitInt(0) < LitInt(1) || (LitInt(0) == LitInt(1) && LitInt(0) < n#0 + 1);
            assume _module.__default.S2N#canCall(tail#0);
            assume _module.__default.S2N_k($LS($LZ), n#0, tail#0)
               == #_module.Number.Zero(_module.__default.S2N($LS($LZ), tail#0));
            assume _module.__default.S2N#canCall(tail#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.S2N_k($LS($LZ), n#0, tail#0), Tclass._module.Number());
        }
        else
        {
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##tail#0 := tail#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##tail#0, Tclass._module.Stream(TInt), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= LitInt(1) || LitInt(1) == LitInt(1);
            assert 0 <= n#0 + 1 || LitInt(1) < LitInt(1) || ##n#0 + 1 == n#0 + 1;
            assert LitInt(1) < LitInt(1) || (LitInt(1) == LitInt(1) && ##n#0 + 1 < n#0 + 1);
            assume _module.__default.S2N_k#canCall(n#0 - 1, tail#0);
            assume _module.__default.S2N_k($LS($LZ), n#0, tail#0)
               == #_module.Number.Succ(_module.__default.S2N_k($LS($LZ), n#0 - 1, tail#0));
            assume _module.__default.S2N_k#canCall(n#0 - 1, tail#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.S2N_k($LS($LZ), n#0, tail#0), Tclass._module.Number());
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.N2S
function _module.__default.N2S($ly: LayerType, r#0: DatatypeType) : DatatypeType;

function _module.__default.N2S#canCall(r#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, r#0: DatatypeType :: 
  { _module.__default.N2S($LS($ly), r#0) } 
  _module.__default.N2S($LS($ly), r#0) == _module.__default.N2S($ly, r#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, r#0: DatatypeType :: 
  { _module.__default.N2S(AsFuelBottom($ly), r#0) } 
  _module.__default.N2S($ly, r#0) == _module.__default.N2S($LZ, r#0));

// consequence axiom for _module.__default.N2S
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, r#0: DatatypeType :: 
    { _module.__default.N2S($ly, r#0) } 
    _module.__default.N2S#canCall(r#0)
         || (35 != $FunctionContextHeight
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> $Is(_module.__default.N2S($ly, r#0), Tclass._module.Stream(TInt)));

function _module.__default.N2S#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.N2S
axiom (forall $ly: LayerType, r#0: DatatypeType :: 
  { _module.__default.N2S#requires($ly, r#0) } 
  $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
     ==> _module.__default.N2S#requires($ly, r#0) == true);

// definition axiom for _module.__default.N2S (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, r#0: DatatypeType :: 
    { _module.__default.N2S($LS($ly), r#0) } 
    _module.__default.N2S#canCall(r#0)
         || (35 != $FunctionContextHeight
           && $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())))
       ==> (!_module.CoOption.None_q(r#0)
           ==> (var num#1 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
            _module.__default.N2S_k#canCall(LitInt(0), num#1)))
         && _module.__default.N2S($LS($ly), r#0)
           == (if _module.CoOption.None_q(r#0)
             then #_module.Stream.Nil()
             else (var num#0 := $Unbox(_module.CoOption.get(r#0)): DatatypeType; 
              _module.__default.N2S_k($ly, LitInt(0), num#0))));

procedure CheckWellformed$$_module.__default.N2S(r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number())));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.N2S(r#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: DatatypeType;
  var num#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##n#0: int;
  var ##num#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function N2S
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(488,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.N2S($LS($LZ), r#0), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (r#0 == #_module.CoOption.None())
        {
            assume _module.__default.N2S($LS($LZ), r#0) == Lit(#_module.Stream.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.N2S($LS($LZ), r#0), Tclass._module.Stream(TInt));
        }
        else if (r#0 == #_module.CoOption.Some($Box(_mcc#0#0)))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number());
            havoc num#Z#0;
            assume $Is(num#Z#0, Tclass._module.Number());
            assume let#0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.Number());
            assume num#Z#0 == let#0#0#0;
            assert $Is(LitInt(0), Tclass._System.nat());
            ##n#0 := LitInt(0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##num#0 := num#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= LitInt(1) || LitInt(0) == LitInt(1);
            assert LitInt(0) <= LitInt(1) && (LitInt(0) == LitInt(1) ==> true);
            assume _module.__default.N2S_k#canCall(LitInt(0), num#Z#0);
            assume _module.__default.N2S($LS($LZ), r#0)
               == _module.__default.N2S_k($LS($LZ), LitInt(0), num#Z#0);
            assume _module.__default.N2S_k#canCall(LitInt(0), num#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.N2S($LS($LZ), r#0), Tclass._module.Stream(TInt));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.N2S'
function _module.__default.N2S_k($ly: LayerType, n#0: int, num#0: DatatypeType) : DatatypeType;

function _module.__default.N2S_k#canCall(n#0: int, num#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int, num#0: DatatypeType :: 
  { _module.__default.N2S_k($LS($ly), n#0, num#0) } 
  _module.__default.N2S_k($LS($ly), n#0, num#0)
     == _module.__default.N2S_k($ly, n#0, num#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int, num#0: DatatypeType :: 
  { _module.__default.N2S_k(AsFuelBottom($ly), n#0, num#0) } 
  _module.__default.N2S_k($ly, n#0, num#0)
     == _module.__default.N2S_k($LZ, n#0, num#0));

// consequence axiom for _module.__default.N2S_k
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int, num#0: DatatypeType :: 
    { _module.__default.N2S_k($ly, n#0, num#0) } 
    _module.__default.N2S_k#canCall(n#0, num#0)
         || (35 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(num#0, Tclass._module.Number()))
       ==> $Is(_module.__default.N2S_k($ly, n#0, num#0), Tclass._module.Stream(TInt)));

function _module.__default.N2S_k#requires(LayerType, int, DatatypeType) : bool;

// #requires axiom for _module.__default.N2S_k
axiom (forall $ly: LayerType, n#0: int, num#0: DatatypeType :: 
  { _module.__default.N2S_k#requires($ly, n#0, num#0) } 
  LitInt(0) <= n#0 && $Is(num#0, Tclass._module.Number())
     ==> _module.__default.N2S_k#requires($ly, n#0, num#0) == true);

// definition axiom for _module.__default.N2S_k (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int, num#0: DatatypeType :: 
    { _module.__default.N2S_k($LS($ly), n#0, num#0) } 
    _module.__default.N2S_k#canCall(n#0, num#0)
         || (35 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(num#0, Tclass._module.Number()))
       ==> (_module.Number.Succ_q(num#0)
           ==> (var next#1 := _module.Number._h4(num#0); 
            _module.__default.N2S_k#canCall(n#0 + 1, next#1)))
         && (!_module.Number.Succ_q(num#0)
           ==> (var r#1 := _module.Number._h5(num#0); _module.__default.N2S#canCall(r#1)))
         && _module.__default.N2S_k($LS($ly), n#0, num#0)
           == (if _module.Number.Succ_q(num#0)
             then (var next#0 := _module.Number._h4(num#0); 
              _module.__default.N2S_k($ly, n#0 + 1, next#0))
             else (var r#0 := _module.Number._h5(num#0); 
              #_module.Stream.Cons($Box(n#0), _module.__default.N2S($ly, r#0)))));

procedure CheckWellformed$$_module.__default.N2S_k(n#0: int where LitInt(0) <= n#0, 
    num#0: DatatypeType where $Is(num#0, Tclass._module.Number()));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.N2S_k(n#0: int, num#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#1#0: DatatypeType;
  var r#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##r#0: DatatypeType;
  var _mcc#0#0: DatatypeType;
  var next#Z#0: DatatypeType;
  var let#1#0#0: DatatypeType;
  var ##n#0: int;
  var ##num#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function N2S'
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(494,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.N2S_k($LS($LZ), n#0, num#0), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (num#0 == #_module.Number.Succ(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number());
            havoc next#Z#0;
            assume $Is(next#Z#0, Tclass._module.Number());
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass._module.Number());
            assume next#Z#0 == let#1#0#0;
            assert $Is(n#0 + 1, Tclass._System.nat());
            ##n#0 := n#0 + 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##num#0 := next#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= LitInt(0) || LitInt(0) == LitInt(0);
            assert LitInt(0) < LitInt(0)
               || (LitInt(0) == LitInt(0) && DtRank(##num#0) < DtRank(num#0));
            assume _module.__default.N2S_k#canCall(n#0 + 1, next#Z#0);
            assume _module.__default.N2S_k($LS($LZ), n#0, num#0)
               == _module.__default.N2S_k($LS($LZ), n#0 + 1, next#Z#0);
            assume _module.__default.N2S_k#canCall(n#0 + 1, next#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.N2S_k($LS($LZ), n#0, num#0), Tclass._module.Stream(TInt));
        }
        else if (num#0 == #_module.Number.Zero(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()));
            havoc r#Z#0;
            assume $Is(r#Z#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume r#Z#0 == let#0#0#0;
            ##r#0 := r#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.N2S#canCall(r#Z#0);
            assume _module.__default.N2S_k($LS($LZ), n#0, num#0)
               == #_module.Stream.Cons($Box(n#0), _module.__default.N2S($LS($LZ), r#Z#0));
            assume _module.__default.N2S#canCall(r#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.N2S_k($LS($LZ), n#0, num#0), Tclass._module.Stream(TInt));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure {:_induction t#0, p#0} CheckWellformed$$_module.__default.Path__Lemma0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  free requires 61 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction t#0, p#0} Call$$_module.__default.Path__Lemma0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  // user-defined preconditions
  requires _module.__default.ValidPath($LS($LS($LZ)), t#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N#canCall(p#0)
     && _module.__default.ValidPath__Alt#canCall(t#0, _module.__default.S2N($LS($LZ), p#0));
  ensures _module.__default.ValidPath__Alt($LS($LS($LZ)), t#0, _module.__default.S2N($LS($LS($LZ)), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction t#0, p#0} Impl$$_module.__default.Path__Lemma0(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0))
   returns ($_reverifyPost: bool);
  free requires 61 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.ValidPath($LS($LS($LZ)), t#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N#canCall(p#0)
     && _module.__default.ValidPath__Alt#canCall(t#0, _module.__default.S2N($LS($LZ), p#0));
  ensures _module.__default.ValidPath__Alt($LS($LS($LZ)), t#0, _module.__default.S2N($LS($LS($LZ)), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction t#0, p#0} Impl$$_module.__default.Path__Lemma0(t#0: DatatypeType, p#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##t#2: DatatypeType;
  var ##p#2: DatatypeType;
  var t##0_0: DatatypeType;
  var p##0_0: DatatypeType;

    // AddMethodImpl: Path_Lemma0, Impl$$_module.__default.Path__Lemma0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(505,0): initial state"} true;
    assume $IsA#_module.Tree(t#0);
    assume $IsA#_module.Stream(p#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#t0#0: DatatypeType, $ih#p0#0: DatatypeType :: 
      $Is($ih#t0#0, Tclass._module.Tree())
           && $Is($ih#p0#0, Tclass._module.Stream(TInt))
           && _module.__default.ValidPath($LS($LZ), $ih#t0#0, $ih#p0#0)
           && DtRank($ih#t0#0) < DtRank(t#0)
         ==> _module.__default.ValidPath__Alt($LS($LZ), $ih#t0#0, _module.__default.S2N($LS($LZ), $ih#p0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(506,3)
    ##t#2 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
    ##p#2 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##p#2, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.ValidPath#canCall(t#0, p#0);
    assume _module.__default.ValidPath#canCall(t#0, p#0);
    if (_module.__default.ValidPath($LS($LZ), t#0, p#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(507,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0_0 := t#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0_0 := p#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Path__Lemma0_k(t##0_0, p##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(507,22)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.Path__Lemma0_k(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Path__Lemma0_k(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  // user-defined preconditions
  requires _module.__default.ValidPath($LS($LS($LZ)), t#0, p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N#canCall(p#0)
     && _module.__default.ValidPath__Alt#canCall(t#0, _module.__default.S2N($LS($LZ), p#0));
  ensures _module.__default.ValidPath__Alt($LS($LS($LZ)), t#0, _module.__default.S2N($LS($LS($LZ)), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, t#1, p#1} CoCall$$_module.__default.Path__Lemma0_k_h(_k#0: Box, 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Tree())
         && $IsAlloc(t#1, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#1), 
    p#1: DatatypeType
       where $Is(p#1, Tclass._module.Stream(TInt))
         && $IsAlloc(p#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#1));
  // user-defined preconditions
  requires _module.__default.ValidPath($LS($LS($LZ)), t#1, p#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N#canCall(p#1)
     && _module.__default.ValidPath__Alt_h#canCall(_k#0, t#1, _module.__default.S2N($LS($LZ), p#1));
  ensures _module.__default.ValidPath__Alt_h($LS($LS($LZ)), _k#0, t#1, _module.__default.S2N($LS($LS($LZ)), p#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, t#1, p#1} Impl$$_module.__default.Path__Lemma0_k_h(_k#0: Box, 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Tree())
         && $IsAlloc(t#1, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#1), 
    p#1: DatatypeType
       where $Is(p#1, Tclass._module.Stream(TInt))
         && $IsAlloc(p#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#1))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.ValidPath($LS($LS($LZ)), t#1, p#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N#canCall(p#1)
     && _module.__default.ValidPath__Alt_h#canCall(_k#0, t#1, _module.__default.S2N($LS($LZ), p#1));
  ensures _module.__default.ValidPath__Alt_h($LS($LS($LZ)), _k#0, t#1, _module.__default.S2N($LS($LS($LZ)), p#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, t#1, p#1} Impl$$_module.__default.Path__Lemma0_k_h(_k#0: Box, t#1: DatatypeType, p#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var tail#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var index#0: int;
  var let#0_0_1#0#0: int;
  var ch#0: DatatypeType
     where $Is(ch#0, Tclass._module.Stream(Tclass._module.Tree()))
       && $IsAlloc(ch#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var ##t#2: DatatypeType;
  var ##p#2: DatatypeType;
  var _k##0: Box;
  var tChildren##0: DatatypeType;
  var n##0: int;
  var tail##0: DatatypeType;
  var ##n#1: int;
  var ##tail#0: DatatypeType;
  var ##_k#0: Box;
  var ##s#1: DatatypeType;
  var ##num#0: DatatypeType;
  var ##n#2: int;
  var ##tail#1: DatatypeType;
  var ##_k#1: Box;
  var ##s#2: DatatypeType;
  var ##num#1: DatatypeType;
  var ##n#3: int;
  var ##tail#2: DatatypeType;
  var ##_k#2: Box;
  var ##t#3: DatatypeType;
  var ##r#1: DatatypeType;
  var ##n#4: int;
  var ##tail#3: DatatypeType;
  var ##_k#3: Box;
  var ##t#4: DatatypeType;
  var ##r#2: DatatypeType;
  var ##p#3: DatatypeType;
  var ##n#5: int;
  var ##tail#4: DatatypeType;
  var ##p#4: DatatypeType;
  var ##_k#4: Box;
  var ##t#5: DatatypeType;
  var ##r#3: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Path_Lemma0'#, Impl$$_module.__default.Path__Lemma0_k_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(510,15): initial state"} true;
    assume $IsA#_module.Tree(t#1);
    assume $IsA#_module.Stream(p#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#t0#0: DatatypeType, $ih#p0#0: DatatypeType :: 
      $Is($ih#t0#0, Tclass._module.Tree())
           && $Is($ih#p0#0, Tclass._module.Stream(TInt))
           && _module.__default.ValidPath($LS($LZ), $ih#t0#0, $ih#p0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && DtRank($ih#t0#0) < DtRank(t#1)))
         ==> _module.__default.ValidPath__Alt_h($LS($LZ), $ih#_k0#0, $ih#t0#0, _module.__default.S2N($LS($LZ), $ih#p0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(513,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (p#1 == #_module.Stream.Nil())
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(516,7)
            assume $IsA#_module.Tree(t#1);
            assert _module.Tree#Equal(t#1, #_module.Tree.Node(Lit(#_module.Stream.Nil())));
        }
        else if (p#1 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.Stream(TInt))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(TInt), $Heap);
            havoc tail#0;
            assume $Is(tail#0, Tclass._module.Stream(TInt))
               && $IsAlloc(tail#0, Tclass._module.Stream(TInt), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(TInt));
            assume tail#0 == let#0_0_0#0#0;
            havoc index#0;
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_1#0#0, TInt);
            assume index#0 == let#0_0_1#0#0;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(518,7)
            assume true;
            assert LitInt(0) <= index#0;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(519,14)
            assume true;
            assume _module.Tree.Node_q(t#1);
            ##s#0 := _module.Tree.children(t#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            assert $Is(index#0, Tclass._System.nat());
            ##n#0 := index#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            assume _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#1), index#0);
            assume _module.Tree.Node_q(t#1)
               && _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Tree.children(t#1), index#0);
            ch#0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Tree.children(t#1), index#0);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(519,39)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(520,7)
            if (_module.Stream.Cons_q(ch#0))
            {
                assert _module.Stream.Cons_q(ch#0);
                ##t#2 := $Unbox(_module.Stream.head(ch#0)): DatatypeType;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
                ##p#2 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#2, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath#canCall($Unbox(_module.Stream.head(ch#0)): DatatypeType, tail#0);
            }

            assume _module.Stream.Cons_q(ch#0)
               ==> _module.__default.ValidPath#canCall($Unbox(_module.Stream.head(ch#0)): DatatypeType, tail#0);
            assert {:subsumption 0} _module.Stream.Cons_q(ch#0);
            assert {:subsumption 0} _module.__default.ValidPath($LS($LS($LZ)), $Unbox(_module.Stream.head(ch#0)): DatatypeType, tail#0);
            assume _module.Stream.Cons_q(ch#0)
               && _module.__default.ValidPath($LS($LZ), $Unbox(_module.Stream.head(ch#0)): DatatypeType, tail#0);
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assume $Is(index#0, Tclass._System.nat());
                ##n#4 := index#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#4, Tclass._System.nat(), $Heap);
                ##tail#3 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#3, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall(index#0, tail#0);
                ##_k#3 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#3, TORDINAL, $Heap);
                ##t#4 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#4, Tclass._module.Tree(), $Heap);
                ##r#2 := #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#2, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.ValidPath__Alt_h#canCall(_k#0, 
                  t#1, 
                  #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0))));
                assume _module.__default.S2N_k#canCall(index#0, tail#0)
                   && _module.__default.ValidPath__Alt_h#canCall(_k#0, 
                    t#1, 
                    #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0))));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assume _module.__default.ValidPath__Alt_h($LS($LZ), 
                  _k#0, 
                  t#1, 
                  #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0))));
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(524,11)
                ##p#3 := p#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#3, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(p#1);
                assert $Is(index#0, Tclass._System.nat());
                ##n#5 := index#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#5, Tclass._System.nat(), $Heap);
                ##tail#4 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#4, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall(index#0, tail#0);
                assume $IsA#_module.CoOption(_module.__default.S2N($LS($LZ), p#1))
                   && 
                  _module.__default.S2N#canCall(p#1)
                   && _module.__default.S2N_k#canCall(index#0, tail#0);
                assert {:subsumption 0} $Eq#_module.CoOption(Tclass._module.Number(), 
                  Tclass._module.Number(), 
                  $LS($LS($LZ)), 
                  _module.__default.S2N($LS($LS($LZ)), p#1), 
                  #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LS($LZ)), index#0, tail#0))));
                assume $Eq#_module.CoOption(Tclass._module.Number(), 
                  Tclass._module.Number(), 
                  $LS($LS($LZ)), 
                  _module.__default.S2N($LS($LZ), p#1), 
                  #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0))));
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                ##p#4 := p#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#4, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(p#1);
                ##_k#4 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#4, TORDINAL, $Heap);
                ##t#5 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#5, Tclass._module.Tree(), $Heap);
                ##r#3 := _module.__default.S2N($LS($LZ), p#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#3, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.ValidPath__Alt_h#canCall(_k#0, t#1, _module.__default.S2N($LS($LZ), p#1));
                assume _module.__default.S2N#canCall(p#1)
                   && _module.__default.ValidPath__Alt_h#canCall(_k#0, t#1, _module.__default.S2N($LS($LZ), p#1));
                // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assert {:subsumption 0} _module.__default.ValidPath__Alt_h($LS($LZ), 
                    _k#0, 
                    t#1, 
                    #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0))))
                   ==> _module.__default.ValidPath__Alt_h($LS($LS($LZ)), _k#0, t#1, _module.__default.S2N($LS($LS($LZ)), p#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assume ORD#IsNat(Lit(ORD#FromNat(1)));
                assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume _module.Tree.Node_q(t#1);
                assume $Is(index#0, Tclass._System.nat());
                ##n#2 := index#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
                ##tail#1 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#1, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall(index#0, tail#0);
                ##_k#1 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#1, TORDINAL, $Heap);
                ##s#2 := _module.Tree.children(t#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#2, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##num#1 := _module.__default.S2N_k($LS($LZ), index#0, tail#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#1, Tclass._module.Number(), $Heap);
                assume _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Tree.children(t#1), 
                  _module.__default.S2N_k($LS($LZ), index#0, tail#0));
                assume _module.Tree.Node_q(t#1)
                   && _module.__default.S2N_k#canCall(index#0, tail#0)
                   && _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.Tree.children(t#1), 
                    _module.__default.S2N_k($LS($LZ), index#0, tail#0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assume _module.__default.ValidPath__Alt_k_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Tree.children(t#1), 
                  _module.__default.S2N_k($LS($LZ), index#0, tail#0));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assert $Is(index#0, Tclass._System.nat());
                ##n#3 := index#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
                ##tail#2 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#2, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall(index#0, tail#0);
                ##_k#2 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#2, TORDINAL, $Heap);
                ##t#3 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#3, Tclass._module.Tree(), $Heap);
                ##r#1 := #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.ValidPath__Alt_h#canCall(_k#0, 
                  t#1, 
                  #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0))));
                assume _module.__default.S2N_k#canCall(index#0, tail#0)
                   && _module.__default.ValidPath__Alt_h#canCall(_k#0, 
                    t#1, 
                    #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), index#0, tail#0))));
                // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assert {:subsumption 0} _module.__default.ValidPath__Alt_k_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.Tree.children(t#1), 
                    _module.__default.S2N_k($LS($LZ), index#0, tail#0))
                   ==> _module.__default.ValidPath__Alt_h($LS($LS($LZ)), 
                    _k#0, 
                    t#1, 
                    #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LS($LZ)), index#0, tail#0))));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assume true;
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assume true;
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(528,24)
                // TrCallStmt: Before ProcessCallStmt
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
                assume _module.Tree.Node_q(t#1);
                assume _module.Tree.Node_q(t#1);
                // ProcessCallStmt: CheckSubrange
                tChildren##0 := _module.Tree.children(t#1);
                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is(index#0, Tclass._System.nat());
                n##0 := index#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                tail##0 := tail#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call CoCall$$_module.__default.Path__Lemma0_k_k_h(_k##0, tChildren##0, n##0, tail##0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(528,48)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume _module.Tree.Node_q(t#1);
                assert $Is(index#0, Tclass._System.nat());
                ##n#1 := index#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
                ##tail#0 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall(index#0, tail#0);
                ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                ##s#1 := _module.Tree.children(t#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##num#0 := _module.__default.S2N_k($LS($LZ), index#0, tail#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
                assume _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.Tree.children(t#1), 
                  _module.__default.S2N_k($LS($LZ), index#0, tail#0));
                assume _module.Tree.Node_q(t#1)
                   && _module.__default.S2N_k#canCall(index#0, tail#0)
                   && _module.__default.ValidPath__Alt_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.Tree.children(t#1), 
                    _module.__default.S2N_k($LS($LZ), index#0, tail#0));
                // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(522,7)
                assert {:subsumption 0} Lit(true)
                   ==> _module.__default.ValidPath__Alt_k_h($LS($LS($LZ)), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.Tree.children(t#1), 
                    _module.__default.S2N_k($LS($LS($LZ)), index#0, tail#0));
                assume false;
            }

            assume true
               ==> _module.__default.ValidPath__Alt_h($LS($LZ), _k#0, t#1, _module.__default.S2N($LS($LZ), p#1));
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(510,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, t#2: DatatypeType, p#2: DatatypeType :: 
          $Is(t#2, Tclass._module.Tree())
               && $Is(p#2, Tclass._module.Stream(TInt))
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.ValidPath($LS($LZ), t#2, p#2)
             ==> _module.__default.ValidPath__Alt_h($LS($LZ), _k'#0, t#2, _module.__default.S2N($LS($LZ), p#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(510,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Path__Lemma0_k_k(tChildren#0: DatatypeType
       where $Is(tChildren#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(tChildren#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(tChildren#0), 
    n#0: int where LitInt(0) <= n#0, 
    tail#0: DatatypeType
       where $Is(tail#0, Tclass._module.Stream(TInt))
         && $IsAlloc(tail#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(tail#0));
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Path__Lemma0_k_k(tChildren#0: DatatypeType, n#0: int, tail#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ch#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var ##t#0: DatatypeType;
  var ##p#0: DatatypeType;
  var ##n#1: int;
  var ##tail#0: DatatypeType;
  var ##s#1: DatatypeType;
  var ##num#0: DatatypeType;

    // AddMethodImpl: Path_Lemma0'', CheckWellformed$$_module.__default.Path__Lemma0_k_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(533,15): initial state"} true;
    havoc ch#Z#0;
    assume $Is(ch#Z#0, Tclass._module.Stream(Tclass._module.Tree()));
    ##s#0 := tChildren#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#0, n#0);
    assume let#0#0#0
       == _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), tChildren#0, n#0);
    assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#0, n#0);
    // CheckWellformedWithResult: any expression
    assume $Is(let#0#0#0, Tclass._module.Stream(Tclass._module.Tree()));
    assume ch#Z#0 == let#0#0#0;
    if (_module.Stream.Cons_q(ch#Z#0))
    {
        assert _module.Stream.Cons_q(ch#Z#0);
        ##t#0 := $Unbox(_module.Stream.head(ch#Z#0)): DatatypeType;
        // assume allocatedness for argument to function
        assume $IsAlloc(##t#0, Tclass._module.Tree(), $Heap);
        ##p#0 := tail#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##p#0, Tclass._module.Stream(TInt), $Heap);
        assume _module.__default.ValidPath#canCall($Unbox(_module.Stream.head(ch#Z#0)): DatatypeType, tail#0);
    }

    assume (var ch#0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), tChildren#0, n#0); 
      _module.Stream.Cons_q(ch#0)
         && _module.__default.ValidPath($LS($LZ), $Unbox(_module.Stream.head(ch#0)): DatatypeType, tail#0));
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(535,24): post-state"} true;
    ##n#1 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    ##tail#0 := tail#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##tail#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.S2N_k#canCall(n#0, tail#0);
    ##s#1 := tChildren#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
    ##num#0 := _module.__default.S2N_k($LS($LZ), n#0, tail#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
    assume _module.__default.ValidPath__Alt_k#canCall(tChildren#0, _module.__default.S2N_k($LS($LZ), n#0, tail#0));
    assume _module.__default.ValidPath__Alt_k($LS($LZ), tChildren#0, _module.__default.S2N_k($LS($LZ), n#0, tail#0));
}



procedure Call$$_module.__default.Path__Lemma0_k_k(tChildren#0: DatatypeType
       where $Is(tChildren#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(tChildren#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(tChildren#0), 
    n#0: int where LitInt(0) <= n#0, 
    tail#0: DatatypeType
       where $Is(tail#0, Tclass._module.Stream(TInt))
         && $IsAlloc(tail#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(tail#0));
  // user-defined preconditions
  requires (var ch#0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#0, n#0); 
    _module.Stream.Cons_q(ch#0));
  requires (var ch#0 := _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#0, n#0); 
    _module.__default.ValidPath($LS($LS($LZ)), $Unbox(_module.Stream.head(ch#0)): DatatypeType, tail#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N_k#canCall(n#0, tail#0)
     && _module.__default.ValidPath__Alt_k#canCall(tChildren#0, _module.__default.S2N_k($LS($LZ), n#0, tail#0));
  ensures _module.__default.ValidPath__Alt_k($LS($LS($LZ)), tChildren#0, _module.__default.S2N_k($LS($LS($LZ)), n#0, tail#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, tChildren#1, n#1, tail#1} CoCall$$_module.__default.Path__Lemma0_k_k_h(_k#0: Box, 
    tChildren#1: DatatypeType
       where $Is(tChildren#1, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(tChildren#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(tChildren#1), 
    n#1: int where LitInt(0) <= n#1, 
    tail#1: DatatypeType
       where $Is(tail#1, Tclass._module.Stream(TInt))
         && $IsAlloc(tail#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(tail#1));
  // user-defined preconditions
  requires (var ch#1 := _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#1, n#1); 
    _module.Stream.Cons_q(ch#1));
  requires (var ch#1 := _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#1, n#1); 
    _module.__default.ValidPath($LS($LS($LZ)), $Unbox(_module.Stream.head(ch#1)): DatatypeType, tail#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N_k#canCall(n#1, tail#1)
     && _module.__default.ValidPath__Alt_k_h#canCall(_k#0, tChildren#1, _module.__default.S2N_k($LS($LZ), n#1, tail#1));
  ensures _module.__default.ValidPath__Alt_k_h($LS($LS($LZ)), 
    _k#0, 
    tChildren#1, 
    _module.__default.S2N_k($LS($LS($LZ)), n#1, tail#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, tChildren#1, n#1, tail#1} Impl$$_module.__default.Path__Lemma0_k_k_h(_k#0: Box, 
    tChildren#1: DatatypeType
       where $Is(tChildren#1, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(tChildren#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(tChildren#1), 
    n#1: int where LitInt(0) <= n#1, 
    tail#1: DatatypeType
       where $Is(tail#1, Tclass._module.Stream(TInt))
         && $IsAlloc(tail#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(tail#1))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  // user-defined preconditions
  requires (var ch#1 := _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#1, n#1); 
    _module.Stream.Cons_q(ch#1));
  requires (var ch#1 := _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#1, n#1); 
    _module.__default.ValidPath($LS($LS($LZ)), $Unbox(_module.Stream.head(ch#1)): DatatypeType, tail#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N_k#canCall(n#1, tail#1)
     && _module.__default.ValidPath__Alt_k_h#canCall(_k#0, tChildren#1, _module.__default.S2N_k($LS($LZ), n#1, tail#1));
  ensures _module.__default.ValidPath__Alt_k_h($LS($LS($LZ)), 
    _k#0, 
    tChildren#1, 
    _module.__default.S2N_k($LS($LS($LZ)), n#1, tail#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, tChildren#1, n#1, tail#1} Impl$$_module.__default.Path__Lemma0_k_k_h(_k#0: Box, tChildren#1: DatatypeType, n#1: int, tail#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var s##0: DatatypeType;
  var k##0: int;
  var n##0: int;
  var ##n#2: int;
  var ##tail#1: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var r#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var _k##0: Box;
  var t##0: DatatypeType;
  var p##0: DatatypeType;
  var _mcc#0#0: DatatypeType;
  var next#0: DatatypeType;
  var let#0_1_0#0#0: DatatypeType;
  var ##s#2: DatatypeType;
  var ##n#3: int;
  var s##1: DatatypeType;
  var n##1: int;
  var ##s#3: DatatypeType;
  var ##n#4: int;
  var ##s#4: DatatypeType;
  var ##n#5: int;
  var s##2: DatatypeType;
  var k##1: int;
  var n##2: int;
  var ##s#5: DatatypeType;
  var ##n#6: int;
  var ##s#6: DatatypeType;
  var ##n#7: int;
  var _k##1: Box;
  var tChildren##0: DatatypeType;
  var n##3: int;
  var tail##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Path_Lemma0''#, Impl$$_module.__default.Path__Lemma0_k_k_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(533,15): initial state"} true;
    assume $IsA#_module.Stream(tChildren#1);
    assume $IsA#_module.Stream(tail#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, 
        $ih#tChildren0#0: DatatypeType, 
        $ih#n0#0: int, 
        $ih#tail0#0: DatatypeType :: 
      $Is($ih#tChildren0#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= $ih#n0#0
           && $Is($ih#tail0#0, Tclass._module.Stream(TInt))
           && (var ch#2 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), $ih#tChildren0#0, $ih#n0#0); 
            _module.Stream.Cons_q(ch#2)
               && _module.__default.ValidPath($LS($LZ), $Unbox(_module.Stream.head(ch#2)): DatatypeType, $ih#tail0#0))
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && 0 <= $ih#n0#0 && $ih#n0#0 < n#1))
         ==> _module.__default.ValidPath__Alt_k_h($LS($LZ), 
          $ih#_k0#0, 
          $ih#tChildren0#0, 
          _module.__default.S2N_k($LS($LZ), $ih#n0#0, $ih#tail0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(536,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(537,14)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        s##0 := tChildren#1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(LitInt(0), Tclass._System.nat());
        k##0 := LitInt(0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0 := n#1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Tail__Lemma1(Tclass._module.Tree(), s##0, k##0, n##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(537,30)"} true;
        ##n#2 := n#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
        ##tail#1 := tail#1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##tail#1, Tclass._module.Stream(TInt), $Heap);
        assume _module.__default.S2N_k#canCall(n#1, tail#1);
        assume _module.__default.S2N_k#canCall(n#1, tail#1);
        havoc _mcc#1#0;
        havoc _mcc#0#0;
        if (_module.__default.S2N_k($LS($LZ), n#1, tail#1) == #_module.Number.Succ(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number())
               && $IsAlloc(_mcc#0#0, Tclass._module.Number(), $Heap);
            havoc next#0;
            assume $Is(next#0, Tclass._module.Number())
               && $IsAlloc(next#0, Tclass._module.Number(), $Heap);
            assume let#0_1_0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_0#0#0, Tclass._module.Number());
            assume next#0 == let#0_1_0#0#0;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                ##s#6 := tChildren#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#6, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#7 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#7, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#1, n#1);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#1, n#1);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                ##s#4 := tChildren#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#4, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#5 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#5, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#1, n#1);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#1, n#1);
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(542,22)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                s##2 := tChildren#1;
                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is(n#1 - 1, Tclass._System.nat());
                k##1 := n#1 - 1;
                assume true;
                // ProcessCallStmt: CheckSubrange
                n##2 := n#1;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Tail__Lemma1(Tclass._module.Tree(), s##2, k##1, n##2);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(542,40)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                ##s#5 := tChildren#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#5, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                assert $Is(n#1 - 1, Tclass._System.nat());
                ##n#6 := n#1 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#6, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#1, n#1 - 1);
                assert _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), tChildren#1, n#1 - 1));
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#1, n#1 - 1);
                // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                assert {:subsumption 0} $Eq#_module.Stream(Tclass._module.Tree(), 
                  Tclass._module.Tree(), 
                  $LS($LS($LZ)), 
                  _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#1, n#1), 
                  _module.Stream.tail(_module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#1, n#1 - 1)));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                ##s#2 := tChildren#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#2, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                assume $Is(n#1 - 1, Tclass._System.nat());
                ##n#3 := n#1 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#1, n#1 - 1);
                assume _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), tChildren#1, n#1 - 1));
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), tChildren#1, n#1 - 1);
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(544,22)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                s##1 := tChildren#1;
                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is(n#1 - 1, Tclass._System.nat());
                n##1 := n#1 - 1;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Tail__Lemma0(Tclass._module.Tree(), s##1, n##1);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(544,37)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                assert _module.Stream.Cons_q(tChildren#1);
                ##s#3 := _module.Stream.tail(tChildren#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#3, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                assert $Is(n#1 - 1, Tclass._System.nat());
                ##n#4 := n#1 - 1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#4, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Stream.tail(tChildren#1), n#1 - 1);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), _module.Stream.tail(tChildren#1), n#1 - 1);
                // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(540,7)
                assert {:subsumption 0} $Eq#_module.Stream(Tclass._module.Tree(), 
                  Tclass._module.Tree(), 
                  $LS($LS($LZ)), 
                  _module.Stream.tail(_module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), tChildren#1, n#1 - 1)), 
                  _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), _module.Stream.tail(tChildren#1), n#1 - 1));
                assume false;
            }

            assume $Eq#_module.Stream(Tclass._module.Tree(), 
              Tclass._module.Tree(), 
              $LS($LS($LZ)), 
              _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), tChildren#1, n#1), 
              _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), _module.Stream.tail(tChildren#1), n#1 - 1));
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(547,20)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##1 := ORD#Minus(_k#0, ORD#FromNat(1));
            assert _module.Stream.Cons_q(tChildren#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            tChildren##0 := _module.Stream.tail(tChildren#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#1 - 1, Tclass._System.nat());
            n##3 := n#1 - 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            tail##0 := tail#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Path__Lemma0_k_k_h(_k##1, tChildren##0, n##3, tail##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(547,46)"} true;
        }
        else if (_module.__default.S2N_k($LS($LZ), n#1, tail#1) == #_module.Number.Zero(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()))
               && $IsAlloc(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            havoc r#0;
            assume $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
               && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume r#0 == let#0_0_0#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(549,19)
            // TrCallStmt: Before ProcessCallStmt
            assert ORD#IsNat(Lit(ORD#FromNat(1)));
            assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
            assert _module.Stream.Cons_q(tChildren#1);
            assume true;
            // ProcessCallStmt: CheckSubrange
            t##0 := $Unbox(_module.Stream.head(tChildren#1)): DatatypeType;
            assume true;
            // ProcessCallStmt: CheckSubrange
            p##0 := tail#1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Path__Lemma0_k_h(_k##0, t##0, p##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(549,40)"} true;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(533,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, tChildren#2: DatatypeType, n#2: int, tail#2: DatatypeType :: 
          $Is(tChildren#2, Tclass._module.Stream(Tclass._module.Tree()))
               && LitInt(0) <= n#2
               && $Is(tail#2, Tclass._module.Stream(TInt))
               && 
              ORD#Less(_k'#0, _k#0)
               && (var ch#3 := _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), tChildren#2, n#2); 
                _module.Stream.Cons_q(ch#3)
                   && _module.__default.ValidPath($LS($LZ), $Unbox(_module.Stream.head(ch#3)): DatatypeType, tail#2))
             ==> _module.__default.ValidPath__Alt_k_h($LS($LZ), _k'#0, tChildren#2, _module.__default.S2N_k($LS($LZ), n#2, tail#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(533,15)"} true;
    }
}



procedure {:_induction t#0, r#0} CheckWellformed$$_module.__default.Path__Lemma1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#0));
  free requires 62 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction t#0, r#0} Call$$_module.__default.Path__Lemma1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#0));
  // user-defined preconditions
  requires _module.__default.ValidPath__Alt($LS($LS($LZ)), t#0, r#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S#canCall(r#0)
     && _module.__default.ValidPath#canCall(t#0, _module.__default.N2S($LS($LZ), r#0));
  ensures _module.__default.ValidPath($LS($LS($LZ)), t#0, _module.__default.N2S($LS($LS($LZ)), r#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction t#0, r#0} Impl$$_module.__default.Path__Lemma1(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#0))
   returns ($_reverifyPost: bool);
  free requires 62 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.ValidPath__Alt($LS($LS($LZ)), t#0, r#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S#canCall(r#0)
     && _module.__default.ValidPath#canCall(t#0, _module.__default.N2S($LS($LZ), r#0));
  ensures _module.__default.ValidPath($LS($LS($LZ)), t#0, _module.__default.N2S($LS($LS($LZ)), r#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction t#0, r#0} Impl$$_module.__default.Path__Lemma1(t#0: DatatypeType, r#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##t#2: DatatypeType;
  var ##r#2: DatatypeType;
  var t##0_0: DatatypeType;
  var r##0_0: DatatypeType;

    // AddMethodImpl: Path_Lemma1, Impl$$_module.__default.Path__Lemma1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(555,0): initial state"} true;
    assume $IsA#_module.Tree(t#0);
    assume $IsA#_module.CoOption(r#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#t0#0: DatatypeType, $ih#r0#0: DatatypeType :: 
      $Is($ih#t0#0, Tclass._module.Tree())
           && $Is($ih#r0#0, Tclass._module.CoOption(Tclass._module.Number()))
           && _module.__default.ValidPath__Alt($LS($LZ), $ih#t0#0, $ih#r0#0)
           && DtRank($ih#t0#0) < DtRank(t#0)
         ==> _module.__default.ValidPath($LS($LZ), $ih#t0#0, _module.__default.N2S($LS($LZ), $ih#r0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(556,3)
    ##t#2 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
    ##r#2 := r#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#2, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
    assume _module.__default.ValidPath__Alt#canCall(t#0, r#0);
    assume _module.__default.ValidPath__Alt#canCall(t#0, r#0);
    if (_module.__default.ValidPath__Alt($LS($LZ), t#0, r#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(557,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        t##0_0 := t#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r##0_0 := r#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Path__Lemma1_k(t##0_0, r##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(557,22)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.Path__Lemma1_k(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#0));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Path__Lemma1_k(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0), 
    r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#0));
  // user-defined preconditions
  requires _module.__default.ValidPath__Alt($LS($LS($LZ)), t#0, r#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S#canCall(r#0)
     && _module.__default.ValidPath#canCall(t#0, _module.__default.N2S($LS($LZ), r#0));
  ensures _module.__default.ValidPath($LS($LS($LZ)), t#0, _module.__default.N2S($LS($LS($LZ)), r#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, t#1, r#1} CoCall$$_module.__default.Path__Lemma1_k_h(_k#0: Box, 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Tree())
         && $IsAlloc(t#1, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#1), 
    r#1: DatatypeType
       where $Is(r#1, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#1, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#1));
  // user-defined preconditions
  requires _module.__default.ValidPath__Alt($LS($LS($LZ)), t#1, r#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S#canCall(r#1)
     && _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S($LS($LZ), r#1));
  ensures _module.__default.ValidPath_h($LS($LS($LZ)), _k#0, t#1, _module.__default.N2S($LS($LS($LZ)), r#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, t#1, r#1} Impl$$_module.__default.Path__Lemma1_k_h(_k#0: Box, 
    t#1: DatatypeType
       where $Is(t#1, Tclass._module.Tree())
         && $IsAlloc(t#1, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#1), 
    r#1: DatatypeType
       where $Is(r#1, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#1, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#1))
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.ValidPath__Alt($LS($LS($LZ)), t#1, r#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S#canCall(r#1)
     && _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S($LS($LZ), r#1));
  ensures _module.__default.ValidPath_h($LS($LS($LZ)), _k#0, t#1, _module.__default.N2S($LS($LS($LZ)), r#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, t#1, r#1} Impl$$_module.__default.Path__Lemma1_k_h(_k#0: Box, t#1: DatatypeType, r#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: DatatypeType;
  var num#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var ##s#0: DatatypeType;
  var ##num#0: DatatypeType;
  var p#0: DatatypeType
     where $Is(p#0, Tclass._module.Stream(TInt))
       && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap);
  var ##n#0: int;
  var ##num#1: DatatypeType;
  var _k##0: Box;
  var s##0: DatatypeType;
  var n##0: int;
  var num##0: DatatypeType;
  var ##n#1: int;
  var ##num#2: DatatypeType;
  var ##_k#0: Box;
  var ##t#2: DatatypeType;
  var ##p#1: DatatypeType;
  var ##n#2: int;
  var ##num#3: DatatypeType;
  var ##_k#1: Box;
  var ##t#3: DatatypeType;
  var ##p#2: DatatypeType;
  var ##r#2: DatatypeType;
  var ##_k#2: Box;
  var ##t#4: DatatypeType;
  var ##p#3: DatatypeType;
  var ##r#3: DatatypeType;
  var ##_k#3: Box;
  var ##t#5: DatatypeType;
  var ##p#4: DatatypeType;
  var ##r#4: DatatypeType;
  var ##_k#4: Box;
  var ##t#6: DatatypeType;
  var ##p#5: DatatypeType;
  var ##r#5: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Path_Lemma1'#, Impl$$_module.__default.Path__Lemma1_k_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(560,15): initial state"} true;
    assume $IsA#_module.Tree(t#1);
    assume $IsA#_module.CoOption(r#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#t0#0: DatatypeType, $ih#r0#0: DatatypeType :: 
      $Is($ih#t0#0, Tclass._module.Tree())
           && $Is($ih#r0#0, Tclass._module.CoOption(Tclass._module.Number()))
           && _module.__default.ValidPath__Alt($LS($LZ), $ih#t0#0, $ih#r0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && 0 <= LitInt(1) && LitInt(1) < LitInt(1)))
         ==> _module.__default.ValidPath_h($LS($LZ), $ih#_k0#0, $ih#t0#0, _module.__default.N2S($LS($LZ), $ih#r0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(564,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0;
        if (r#1 == #_module.CoOption.None())
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(567,7)
            assume $IsA#_module.Tree(t#1);
            assert _module.Tree#Equal(t#1, #_module.Tree.Node(Lit(#_module.Stream.Nil())));
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(568,7)
            ##r#5 := r#1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#5, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            assume _module.__default.N2S#canCall(r#1);
            assume $IsA#_module.Stream(_module.__default.N2S($LS($LZ), r#1))
               && _module.__default.N2S#canCall(r#1);
            assert {:subsumption 0} $Eq#_module.Stream(TInt, 
              TInt, 
              $LS($LS($LZ)), 
              _module.__default.N2S($LS($LS($LZ)), r#1), 
              #_module.Stream.Nil());
            assume $Eq#_module.Stream(TInt, 
              TInt, 
              $LS($LS($LZ)), 
              _module.__default.N2S($LS($LZ), r#1), 
              #_module.Stream.Nil());
        }
        else if (r#1 == #_module.CoOption.Some($Box(_mcc#0#0)))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number())
               && $IsAlloc(_mcc#0#0, Tclass._module.Number(), $Heap);
            havoc num#0;
            assume $Is(num#0, Tclass._module.Number())
               && $IsAlloc(num#0, Tclass._module.Number(), $Heap);
            assume let#0_0_0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Number());
            assume num#0 == let#0_0_0#0#0;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(570,7)
            assume _module.Tree.Node_q(t#1);
            ##s#0 := _module.Tree.children(t#1);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
            ##num#0 := num#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
            assume _module.__default.ValidPath__Alt_k#canCall(_module.Tree.children(t#1), num#0);
            assume _module.Tree.Node_q(t#1)
               && _module.__default.ValidPath__Alt_k#canCall(_module.Tree.children(t#1), num#0);
            assert {:subsumption 0} _module.__default.ValidPath__Alt_k($LS($LS($LZ)), _module.Tree.children(t#1), num#0);
            assume _module.__default.ValidPath__Alt_k($LS($LZ), _module.Tree.children(t#1), num#0);
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(573,13)
            assume true;
            assert $Is(LitInt(0), Tclass._System.nat());
            ##n#0 := LitInt(0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##num#1 := num#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##num#1, Tclass._module.Number(), $Heap);
            assume _module.__default.N2S_k#canCall(LitInt(0), num#0);
            assume _module.__default.N2S_k#canCall(LitInt(0), num#0);
            p#0 := _module.__default.N2S_k($LS($LZ), LitInt(0), num#0);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(573,27)"} true;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                ##r#3 := #_module.CoOption.Some($Box(num#0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#3, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(#_module.CoOption.Some($Box(num#0)));
                ##_k#3 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#3, TORDINAL, $Heap);
                ##t#5 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#5, Tclass._module.Tree(), $Heap);
                ##p#4 := _module.__default.N2S($LS($LZ), #_module.CoOption.Some($Box(num#0)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#4, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S($LS($LZ), #_module.CoOption.Some($Box(num#0))));
                assume _module.__default.N2S#canCall(#_module.CoOption.Some($Box(num#0)))
                   && _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S($LS($LZ), #_module.CoOption.Some($Box(num#0))));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assume _module.__default.ValidPath_h($LS($LZ), 
                  _k#0, 
                  t#1, 
                  _module.__default.N2S($LS($LZ), #_module.CoOption.Some($Box(num#0))));
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                ##r#4 := r#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#4, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#1);
                ##_k#4 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#4, TORDINAL, $Heap);
                ##t#6 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#6, Tclass._module.Tree(), $Heap);
                ##p#5 := _module.__default.N2S($LS($LZ), r#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#5, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S($LS($LZ), r#1));
                assume _module.__default.N2S#canCall(r#1)
                   && _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S($LS($LZ), r#1));
                // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assert {:subsumption 0} _module.__default.ValidPath_h($LS($LZ), 
                    _k#0, 
                    t#1, 
                    _module.__default.N2S($LS($LZ), #_module.CoOption.Some($Box(num#0))))
                   ==> _module.__default.ValidPath_h($LS($LS($LZ)), _k#0, t#1, _module.__default.N2S($LS($LS($LZ)), r#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assume $Is(LitInt(0), Tclass._System.nat());
                ##n#2 := LitInt(0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
                ##num#3 := num#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#3, Tclass._module.Number(), $Heap);
                assume _module.__default.N2S_k#canCall(LitInt(0), num#0);
                ##_k#1 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#1, TORDINAL, $Heap);
                ##t#3 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#3, Tclass._module.Tree(), $Heap);
                ##p#2 := _module.__default.N2S_k($LS($LZ), LitInt(0), num#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#2, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S_k($LS($LZ), LitInt(0), num#0));
                assume _module.__default.N2S_k#canCall(LitInt(0), num#0)
                   && _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S_k($LS($LZ), LitInt(0), num#0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assume _module.__default.ValidPath_h($LS($LZ), _k#0, t#1, _module.__default.N2S_k($LS($LZ), LitInt(0), num#0));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                ##r#2 := #_module.CoOption.Some($Box(num#0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#2, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(#_module.CoOption.Some($Box(num#0)));
                ##_k#2 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#2, TORDINAL, $Heap);
                ##t#4 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#4, Tclass._module.Tree(), $Heap);
                ##p#3 := _module.__default.N2S($LS($LZ), #_module.CoOption.Some($Box(num#0)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#3, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S($LS($LZ), #_module.CoOption.Some($Box(num#0))));
                assume _module.__default.N2S#canCall(#_module.CoOption.Some($Box(num#0)))
                   && _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S($LS($LZ), #_module.CoOption.Some($Box(num#0))));
                // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assert {:subsumption 0} _module.__default.ValidPath_h($LS($LZ), _k#0, t#1, _module.__default.N2S_k($LS($LZ), LitInt(0), num#0))
                   ==> _module.__default.ValidPath_h($LS($LS($LZ)), 
                    _k#0, 
                    t#1, 
                    _module.__default.N2S($LS($LS($LZ)), #_module.CoOption.Some($Box(num#0))));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assume true;
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assume true;
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(578,29)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                _k##0 := _k#0;
                assume _module.Tree.Node_q(t#1);
                assume _module.Tree.Node_q(t#1);
                // ProcessCallStmt: CheckSubrange
                s##0 := _module.Tree.children(t#1);
                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is(LitInt(0), Tclass._System.nat());
                n##0 := LitInt(0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                num##0 := num#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert 0 <= LitInt(1)
                   || 
                  _k##0 == _k#0
                   || ORD#Less(_k##0, _k#0)
                   || LitInt(0) == LitInt(1);
                assert (_k##0 == _k#0 || ORD#Less(_k##0, _k#0))
                   && (_k##0 == _k#0 ==> LitInt(0) <= LitInt(1) && (LitInt(0) == LitInt(1) ==> true));
                // ProcessCallStmt: Make the call
                call CoCall$$_module.__default.Path__Lemma1_k_k_h(_k##0, s##0, n##0, num##0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(578,48)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assert $Is(LitInt(0), Tclass._System.nat());
                ##n#1 := LitInt(0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
                ##num#2 := num#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#2, Tclass._module.Number(), $Heap);
                assume _module.__default.N2S_k#canCall(LitInt(0), num#0);
                ##_k#0 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                ##t#2 := t#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
                ##p#1 := _module.__default.N2S_k($LS($LZ), LitInt(0), num#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#1, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S_k($LS($LZ), LitInt(0), num#0));
                assume _module.__default.N2S_k#canCall(LitInt(0), num#0)
                   && _module.__default.ValidPath_h#canCall(_k#0, t#1, _module.__default.N2S_k($LS($LZ), LitInt(0), num#0));
                // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(574,7)
                assert {:subsumption 0} Lit(true)
                   ==> _module.__default.ValidPath_h($LS($LS($LZ)), 
                    _k#0, 
                    t#1, 
                    _module.__default.N2S_k($LS($LS($LZ)), LitInt(0), num#0));
                assume false;
            }

            assume true
               ==> _module.__default.ValidPath_h($LS($LZ), _k#0, t#1, _module.__default.N2S($LS($LZ), r#1));
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(560,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, t#2: DatatypeType, r#2: DatatypeType :: 
          $Is(t#2, Tclass._module.Tree())
               && $Is(r#2, Tclass._module.CoOption(Tclass._module.Number()))
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.ValidPath__Alt($LS($LZ), t#2, r#2)
             ==> _module.__default.ValidPath_h($LS($LZ), _k'#0, t#2, _module.__default.N2S($LS($LZ), r#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(560,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Path__Lemma1_k_k(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0, 
    num#0: DatatypeType
       where $Is(num#0, Tclass._module.Number())
         && $IsAlloc(num#0, Tclass._module.Number(), $Heap)
         && $IsA#_module.Number(num#0));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Path__Lemma1_k_k(s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#0, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#0), 
    n#0: int where LitInt(0) <= n#0, 
    num#0: DatatypeType
       where $Is(num#0, Tclass._module.Number())
         && $IsAlloc(num#0, Tclass._module.Number(), $Heap)
         && $IsA#_module.Number(num#0));
  // user-defined preconditions
  requires _module.__default.ValidPath__Alt_k($LS($LS($LZ)), 
    _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#0, n#0), 
    num#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S_k#canCall(n#0, num#0)
     && _module.__default.ValidPath#canCall(#_module.Tree.Node(s#0), _module.__default.N2S_k($LS($LZ), n#0, num#0));
  ensures _module.__default.ValidPath($LS($LS($LZ)), 
    #_module.Tree.Node(s#0), 
    _module.__default.N2S_k($LS($LS($LZ)), n#0, num#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, n#1, num#1} CoCall$$_module.__default.Path__Lemma1_k_k_h(_k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#1), 
    n#1: int where LitInt(0) <= n#1, 
    num#1: DatatypeType
       where $Is(num#1, Tclass._module.Number())
         && $IsAlloc(num#1, Tclass._module.Number(), $Heap)
         && $IsA#_module.Number(num#1));
  // user-defined preconditions
  requires _module.__default.ValidPath__Alt_k($LS($LS($LZ)), 
    _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#1, n#1), 
    num#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S_k#canCall(n#1, num#1)
     && _module.__default.ValidPath_h#canCall(_k#0, #_module.Tree.Node(s#1), _module.__default.N2S_k($LS($LZ), n#1, num#1));
  ensures _module.__default.ValidPath_h($LS($LS($LZ)), 
    _k#0, 
    #_module.Tree.Node(s#1), 
    _module.__default.N2S_k($LS($LS($LZ)), n#1, num#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, s#1, n#1, num#1} Impl$$_module.__default.Path__Lemma1_k_k_h(_k#0: Box, 
    s#1: DatatypeType
       where $Is(s#1, Tclass._module.Stream(Tclass._module.Tree()))
         && $IsAlloc(s#1, Tclass._module.Stream(Tclass._module.Tree()), $Heap)
         && $IsA#_module.Stream(s#1), 
    n#1: int where LitInt(0) <= n#1, 
    num#1: DatatypeType
       where $Is(num#1, Tclass._module.Number())
         && $IsAlloc(num#1, Tclass._module.Number(), $Heap)
         && $IsA#_module.Number(num#1))
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.ValidPath__Alt_k($LS($LS($LZ)), 
    _module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#1, n#1), 
    num#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S_k#canCall(n#1, num#1)
     && _module.__default.ValidPath_h#canCall(_k#0, #_module.Tree.Node(s#1), _module.__default.N2S_k($LS($LZ), n#1, num#1));
  ensures _module.__default.ValidPath_h($LS($LS($LZ)), 
    _k#0, 
    #_module.Tree.Node(s#1), 
    _module.__default.N2S_k($LS($LS($LZ)), n#1, num#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, s#1, n#1, num#1} Impl$$_module.__default.Path__Lemma1_k_k_h(_k#0: Box, s#1: DatatypeType, n#1: int, num#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#1#0: DatatypeType;
  var r#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var _k##0: Box;
  var t##0: DatatypeType;
  var ##s#2: DatatypeType;
  var ##n#2: int;
  var r##0: DatatypeType;
  var ##s#3: DatatypeType;
  var ##n#3: int;
  var ##r#0: DatatypeType;
  var ##_k#0: Box;
  var ##t#1: DatatypeType;
  var ##p#1: DatatypeType;
  var ##s#4: DatatypeType;
  var ##n#4: int;
  var ##r#1: DatatypeType;
  var ##_k#1: Box;
  var ##t#2: DatatypeType;
  var ##p#2: DatatypeType;
  var ##s#5: DatatypeType;
  var ##n#5: int;
  var ##s#6: DatatypeType;
  var ##n#6: int;
  var ##s#7: DatatypeType;
  var ##n#7: int;
  var ##r#2: DatatypeType;
  var ##_k#2: Box;
  var ##t#3: DatatypeType;
  var ##p#3: DatatypeType;
  var ##s#8: DatatypeType;
  var ##n#8: int;
  var ##s#9: DatatypeType;
  var ##n#9: int;
  var ##r#3: DatatypeType;
  var ##_k#3: Box;
  var ##t#4: DatatypeType;
  var ##p#4: DatatypeType;
  var ##r#4: DatatypeType;
  var ##_k#4: Box;
  var ##t#5: DatatypeType;
  var ##p#5: DatatypeType;
  var ##r#5: DatatypeType;
  var ##_k#5: Box;
  var ##t#6: DatatypeType;
  var ##p#6: DatatypeType;
  var ##n#10: int;
  var ##num#2: DatatypeType;
  var ##_k#6: Box;
  var ##t#7: DatatypeType;
  var ##p#7: DatatypeType;
  var _mcc#0#0: DatatypeType;
  var next#0: DatatypeType;
  var let#0_1_0#0#0: DatatypeType;
  var _k##1: Box;
  var s##0: DatatypeType;
  var n##0: int;
  var num##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Path_Lemma1''#, Impl$$_module.__default.Path__Lemma1_k_k_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(583,15): initial state"} true;
    assume $IsA#_module.Stream(s#1);
    assume $IsA#_module.Number(num#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#s0#0: DatatypeType, $ih#n0#0: int, $ih#num0#0: DatatypeType :: 
      $Is($ih#s0#0, Tclass._module.Stream(Tclass._module.Tree()))
           && LitInt(0) <= $ih#n0#0
           && $Is($ih#num0#0, Tclass._module.Number())
           && _module.__default.ValidPath__Alt_k($LS($LZ), 
            _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), $ih#s0#0, $ih#n0#0), 
            $ih#num0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0
               && ((0 <= LitInt(0) && LitInt(0) < LitInt(0))
                 || (LitInt(0) == LitInt(0) && DtRank($ih#num0#0) < DtRank(num#1)))))
         ==> _module.__default.ValidPath_h($LS($LZ), 
          $ih#_k0#0, 
          #_module.Tree.Node($ih#s0#0), 
          _module.__default.N2S_k($LS($LZ), $ih#n0#0, $ih#num0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(587,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#1#0;
        havoc _mcc#0#0;
        if (num#1 == #_module.Number.Succ(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number())
               && $IsAlloc(_mcc#0#0, Tclass._module.Number(), $Heap);
            havoc next#0;
            assume $Is(next#0, Tclass._module.Number())
               && $IsAlloc(next#0, Tclass._module.Number(), $Heap);
            assume let#0_1_0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_0#0#0, Tclass._module.Number());
            assume next#0 == let#0_1_0#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(590,25)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##1 := _k#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            s##0 := s#1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#1 + 1, Tclass._System.nat());
            n##0 := n#1 + 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            num##0 := next#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= LitInt(0) || ORD#Less(_k##1, _k#0) || LitInt(0) == LitInt(0);
            assert ORD#Less(_k##1, _k#0)
               || (_k##1 == _k#0
                 && (LitInt(0) < LitInt(0)
                   || (LitInt(0) == LitInt(0) && DtRank(num##0) < DtRank(num#1))));
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Path__Lemma1_k_k_h(_k##1, s##0, n##0, num##0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(590,38)"} true;
        }
        else if (num#1 == #_module.Number.Zero(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()))
               && $IsAlloc(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            havoc r#0;
            assume $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
               && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume r#0 == let#0_0_0#0#0;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                ##r#5 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#5, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#0);
                ##_k#5 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#5, TORDINAL, $Heap);
                ##t#6 := #_module.Tree.Node(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#6, Tclass._module.Tree(), $Heap);
                ##p#6 := #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#6, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(_k#0, 
                  #_module.Tree.Node(s#1), 
                  #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                assume _module.__default.N2S#canCall(r#0)
                   && _module.__default.ValidPath_h#canCall(_k#0, 
                    #_module.Tree.Node(s#1), 
                    #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assume _module.__default.ValidPath_h($LS($LZ), 
                  _k#0, 
                  #_module.Tree.Node(s#1), 
                  #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                ##n#10 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#10, Tclass._System.nat(), $Heap);
                ##num#2 := num#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#2, Tclass._module.Number(), $Heap);
                assume _module.__default.N2S_k#canCall(n#1, num#1);
                ##_k#6 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#6, TORDINAL, $Heap);
                ##t#7 := #_module.Tree.Node(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#7, Tclass._module.Tree(), $Heap);
                ##p#7 := _module.__default.N2S_k($LS($LZ), n#1, num#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#7, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(_k#0, #_module.Tree.Node(s#1), _module.__default.N2S_k($LS($LZ), n#1, num#1));
                assume _module.__default.N2S_k#canCall(n#1, num#1)
                   && _module.__default.ValidPath_h#canCall(_k#0, #_module.Tree.Node(s#1), _module.__default.N2S_k($LS($LZ), n#1, num#1));
                // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assert {:subsumption 0} _module.__default.ValidPath_h($LS($LZ), 
                    _k#0, 
                    #_module.Tree.Node(s#1), 
                    #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)))
                   ==> _module.__default.ValidPath_h($LS($LS($LZ)), 
                    _k#0, 
                    #_module.Tree.Node(s#1), 
                    _module.__default.N2S_k($LS($LS($LZ)), n#1, num#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                ##s#8 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#8, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#8 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#8, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                if (_module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1)))
                {
                    assume ORD#IsNat(Lit(ORD#FromNat(1)));
                    assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                    ##s#9 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#9, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                    ##n#9 := n#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##n#9, Tclass._System.nat(), $Heap);
                    assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                    assume _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1));
                    ##r#3 := r#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##r#3, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                    assume _module.__default.N2S#canCall(r#0);
                    ##_k#3 := ORD#Minus(_k#0, ORD#FromNat(1));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##_k#3, TORDINAL, $Heap);
                    ##t#4 := $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#4, Tclass._module.Tree(), $Heap);
                    ##p#4 := _module.__default.N2S($LS($LZ), r#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##p#4, Tclass._module.Stream(TInt), $Heap);
                    assume _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                      $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                      _module.__default.N2S($LS($LZ), r#0));
                }

                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1)
                   && (_module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))
                     ==> _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1)
                       && _module.__default.N2S#canCall(r#0)
                       && _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                        $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                        _module.__default.N2S($LS($LZ), r#0)));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assume _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))
                   && _module.__default.ValidPath_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                    _module.__default.N2S($LS($LZ), r#0));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                ##r#4 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#4, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#0);
                ##_k#4 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#4, TORDINAL, $Heap);
                ##t#5 := #_module.Tree.Node(s#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#5, Tclass._module.Tree(), $Heap);
                ##p#5 := #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#5, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(_k#0, 
                  #_module.Tree.Node(s#1), 
                  #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                assume _module.__default.N2S#canCall(r#0)
                   && _module.__default.ValidPath_h#canCall(_k#0, 
                    #_module.Tree.Node(s#1), 
                    #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assert {:subsumption 0} _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))
                     && _module.__default.ValidPath_h($LS($LZ), 
                      ORD#Minus(_k#0, ORD#FromNat(1)), 
                      $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                      _module.__default.N2S($LS($LZ), r#0))
                   ==> _module.__default.ValidPath_h($LS($LS($LZ)), 
                    _k#0, 
                    #_module.Tree.Node(s#1), 
                    #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LS($LZ)), r#0)));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assume ORD#IsNat(Lit(ORD#FromNat(1)));
                assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                ##s#4 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#4, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#4 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#4, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                assume _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1));
                ##r#1 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#0);
                ##_k#1 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#1, TORDINAL, $Heap);
                ##t#2 := $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
                ##p#2 := _module.__default.N2S($LS($LZ), r#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#2, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                  $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                  _module.__default.N2S($LS($LZ), r#0));
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1)
                   && _module.__default.N2S#canCall(r#0)
                   && _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                    _module.__default.N2S($LS($LZ), r#0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assume _module.__default.ValidPath_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                  _module.__default.N2S($LS($LZ), r#0));
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(596,11)
                ##s#5 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#5, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#5 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#5, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                assert {:subsumption 0} _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#1, n#1));
                assume _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1));
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                ##s#6 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#6, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#6 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#6, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                if (_module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1)))
                {
                    assert ORD#IsNat(Lit(ORD#FromNat(1)));
                    assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                    ##s#7 := s#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##s#7, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                    ##n#7 := n#1;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##n#7, Tclass._System.nat(), $Heap);
                    assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                    assert _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1));
                    ##r#2 := r#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##r#2, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                    assume _module.__default.N2S#canCall(r#0);
                    ##_k#2 := ORD#Minus(_k#0, ORD#FromNat(1));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##_k#2, TORDINAL, $Heap);
                    ##t#3 := $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##t#3, Tclass._module.Tree(), $Heap);
                    ##p#3 := _module.__default.N2S($LS($LZ), r#0);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##p#3, Tclass._module.Stream(TInt), $Heap);
                    assume _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                      $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                      _module.__default.N2S($LS($LZ), r#0));
                }

                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1)
                   && (_module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))
                     ==> _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1)
                       && _module.__default.N2S#canCall(r#0)
                       && _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                        $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                        _module.__default.N2S($LS($LZ), r#0)));
                // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assert {:subsumption 0} _module.__default.ValidPath_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                    _module.__default.N2S($LS($LZ), r#0))
                   ==> _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#1, n#1));
                assert {:subsumption 0} _module.__default.ValidPath_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                    _module.__default.N2S($LS($LZ), r#0))
                   ==> _module.__default.ValidPath_h($LS($LS($LZ)), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#1, n#1))): DatatypeType, 
                    _module.__default.N2S($LS($LS($LZ)), r#0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assume true;
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assume true;
                // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(598,23)
                // TrCallStmt: Before ProcessCallStmt
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
                ##s#2 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#2, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#2 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                assert _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1));
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                // ProcessCallStmt: CheckSubrange
                t##0 := $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType;
                assume true;
                // ProcessCallStmt: CheckSubrange
                r##0 := r#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert 0 <= LitInt(0) || ORD#Less(_k##0, _k#0) || LitInt(1) == LitInt(0);
                assert ORD#Less(_k##0, _k#0) || (_k##0 == _k#0 && LitInt(1) < LitInt(0));
                // ProcessCallStmt: Make the call
                call CoCall$$_module.__default.Path__Lemma1_k_h(_k##0, t##0, r##0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(598,42)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                ##s#3 := s#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#3, Tclass._module.Stream(Tclass._module.Tree()), $Heap);
                ##n#3 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1);
                assert _module.Stream.Cons_q(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1));
                ##r#0 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#0);
                ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                ##t#1 := $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#1, Tclass._module.Tree(), $Heap);
                ##p#1 := _module.__default.N2S($LS($LZ), r#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#1, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                  $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                  _module.__default.N2S($LS($LZ), r#0));
                assume _module.__default.Tail#canCall(Tclass._module.Tree(), s#1, n#1)
                   && _module.__default.N2S#canCall(r#0)
                   && _module.__default.ValidPath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#1, n#1))): DatatypeType, 
                    _module.__default.N2S($LS($LZ), r#0));
                // ----- assert line3 <== line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(592,7)
                assert {:subsumption 0} Lit(true)
                   ==> _module.__default.ValidPath_h($LS($LS($LZ)), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    $Unbox(_module.Stream.head(_module.__default.Tail(Tclass._module.Tree(), $LS($LS($LZ)), s#1, n#1))): DatatypeType, 
                    _module.__default.N2S($LS($LS($LZ)), r#0));
                assume false;
            }

            assume true
               ==> _module.__default.ValidPath_h($LS($LZ), 
                _k#0, 
                #_module.Tree.Node(s#1), 
                _module.__default.N2S_k($LS($LZ), n#1, num#1));
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(583,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, s#2: DatatypeType, n#2: int, num#2: DatatypeType :: 
          $Is(s#2, Tclass._module.Stream(Tclass._module.Tree()))
               && LitInt(0) <= n#2
               && $Is(num#2, Tclass._module.Number())
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.ValidPath__Alt_k($LS($LZ), 
                _module.__default.Tail(Tclass._module.Tree(), $LS($LZ), s#2, n#2), 
                num#2)
             ==> _module.__default.ValidPath_h($LS($LZ), 
              _k'#0, 
              #_module.Tree.Node(s#2), 
              _module.__default.N2S_k($LS($LZ), n#2, num#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(583,15)"} true;
    }
}



procedure {:_induction p#0} CheckWellformed$$_module.__default.Path__Lemma2(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  free requires 63 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction p#0} Call$$_module.__default.Path__Lemma2(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsNeverEndingStream#canCall(TInt, p#0)
     && (_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0)
       ==> _module.__default.S2N#canCall(p#0)
         && _module.__default.InfinitePath#canCall(_module.__default.S2N($LS($LZ), p#0)));
  ensures _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0)
     ==> _module.__default.InfinitePath($LS($LS($LZ)), _module.__default.S2N($LS($LS($LZ)), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction p#0} Impl$$_module.__default.Path__Lemma2(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0))
   returns ($_reverifyPost: bool);
  free requires 63 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.IsNeverEndingStream#canCall(TInt, p#0)
     && (_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0)
       ==> _module.__default.S2N#canCall(p#0)
         && _module.__default.InfinitePath#canCall(_module.__default.S2N($LS($LZ), p#0)));
  ensures _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0)
     ==> _module.__default.InfinitePath($LS($LS($LZ)), _module.__default.S2N($LS($LS($LZ)), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction p#0} Impl$$_module.__default.Path__Lemma2(p#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##s#1: DatatypeType;
  var p##0_0: DatatypeType;

    // AddMethodImpl: Path_Lemma2, Impl$$_module.__default.Path__Lemma2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(605,0): initial state"} true;
    assume $IsA#_module.Stream(p#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#p0#0: DatatypeType :: 
      $Is($ih#p0#0, Tclass._module.Stream(TInt)) && Lit(true) && false
         ==> 
        _module.__default.IsNeverEndingStream(TInt, $LS($LZ), $ih#p0#0)
         ==> _module.__default.InfinitePath($LS($LZ), _module.__default.S2N($LS($LZ), $ih#p0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(606,3)
    ##s#1 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
    assume _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
    if (_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(607,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0_0 := p#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Path__Lemma2_k(p##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(607,19)"} true;
    }
    else
    {
    }
}



procedure CheckWellformed$$_module.__default.Path__Lemma2_k(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Path__Lemma2_k(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0));
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N#canCall(p#0)
     && _module.__default.InfinitePath#canCall(_module.__default.S2N($LS($LZ), p#0));
  ensures _module.__default.InfinitePath($LS($LS($LZ)), _module.__default.S2N($LS($LS($LZ)), p#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, p#1} CoCall$$_module.__default.Path__Lemma2_k_h(_k#0: Box, 
    p#1: DatatypeType
       where $Is(p#1, Tclass._module.Stream(TInt))
         && $IsAlloc(p#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#1));
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N#canCall(p#1)
     && _module.__default.InfinitePath_h#canCall(_k#0, _module.__default.S2N($LS($LZ), p#1));
  ensures _module.__default.InfinitePath_h($LS($LS($LZ)), _k#0, _module.__default.S2N($LS($LS($LZ)), p#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, p#1} Impl$$_module.__default.Path__Lemma2_k_h(_k#0: Box, 
    p#1: DatatypeType
       where $Is(p#1, Tclass._module.Stream(TInt))
         && $IsAlloc(p#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#1))
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N#canCall(p#1)
     && _module.__default.InfinitePath_h#canCall(_k#0, _module.__default.S2N($LS($LZ), p#1));
  ensures _module.__default.InfinitePath_h($LS($LS($LZ)), _k#0, _module.__default.S2N($LS($LS($LZ)), p#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, p#1} Impl$$_module.__default.Path__Lemma2_k_h(_k#0: Box, p#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var tail#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var n#0: int;
  var let#0_0_1#0#0: int;
  var _k##0: Box;
  var p##0: DatatypeType;
  var ##p#1: DatatypeType;
  var ##_k#0: Box;
  var ##r#1: DatatypeType;
  var ##p#2: DatatypeType;
  var ##_k#1: Box;
  var ##r#2: DatatypeType;
  var _k##1: Box;
  var p##1: DatatypeType;
  var n##0: int;
  var tail##0: DatatypeType;
  var ##n#0: int;
  var ##tail#0: DatatypeType;
  var ##_k#2: Box;
  var ##num#0: DatatypeType;
  var ##n#1: int;
  var ##tail#1: DatatypeType;
  var ##_k#3: Box;
  var ##num#1: DatatypeType;
  var ##n#2: int;
  var ##tail#2: DatatypeType;
  var ##_k#4: Box;
  var ##r#3: DatatypeType;
  var ##n#3: int;
  var ##tail#3: DatatypeType;
  var ##_k#5: Box;
  var ##r#4: DatatypeType;
  var ##p#3: DatatypeType;
  var ##_k#6: Box;
  var ##r#5: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Path_Lemma2'#, Impl$$_module.__default.Path__Lemma2_k_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(610,15): initial state"} true;
    assume $IsA#_module.Stream(p#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#p0#0: DatatypeType :: 
      $Is($ih#p0#0, Tclass._module.Stream(TInt))
           && _module.__default.IsNeverEndingStream(TInt, $LS($LZ), $ih#p0#0)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> _module.__default.InfinitePath_h($LS($LZ), $ih#_k0#0, _module.__default.S2N($LS($LZ), $ih#p0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(613,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#0#0, _mcc#1#0;
        if (p#1 == #_module.Stream.Cons($Box(_mcc#0#0), _mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.Stream(TInt))
               && $IsAlloc(_mcc#1#0, Tclass._module.Stream(TInt), $Heap);
            havoc tail#0;
            assume $Is(tail#0, Tclass._module.Stream(TInt))
               && $IsAlloc(tail#0, Tclass._module.Stream(TInt), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Stream(TInt));
            assume tail#0 == let#0_0_0#0#0;
            havoc n#0;
            assume let#0_0_1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_1#0#0, TInt);
            assume n#0 == let#0_0_1#0#0;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                if (n#0 < 0)
                {
                }
                else
                {
                }

                assume $Is((if n#0 < 0 then 0 else n#0), Tclass._System.nat());
                ##n#3 := (if n#0 < 0 then 0 else n#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
                ##tail#3 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#3, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall((if n#0 < 0 then 0 else n#0), tail#0);
                ##_k#5 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#5, TORDINAL, $Heap);
                ##r#4 := #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#4, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.InfinitePath_h#canCall(_k#0, 
                  #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0))));
                assume _module.__default.S2N_k#canCall((if n#0 < 0 then 0 else n#0), tail#0)
                   && _module.__default.InfinitePath_h#canCall(_k#0, 
                    #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0))));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assume _module.__default.InfinitePath_h($LS($LZ), 
                  _k#0, 
                  #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0))));
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                ##p#3 := p#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#3, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(p#1);
                ##_k#6 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#6, TORDINAL, $Heap);
                ##r#5 := _module.__default.S2N($LS($LZ), p#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#5, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.InfinitePath_h#canCall(_k#0, _module.__default.S2N($LS($LZ), p#1));
                assume _module.__default.S2N#canCall(p#1)
                   && _module.__default.InfinitePath_h#canCall(_k#0, _module.__default.S2N($LS($LZ), p#1));
                // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assert {:subsumption 0} _module.__default.InfinitePath_h($LS($LZ), 
                    _k#0, 
                    #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0))))
                   ==> _module.__default.InfinitePath_h($LS($LS($LZ)), _k#0, _module.__default.S2N($LS($LS($LZ)), p#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assume ORD#IsNat(Lit(ORD#FromNat(1)));
                assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                if (n#0 < 0)
                {
                }
                else
                {
                }

                assume $Is((if n#0 < 0 then 0 else n#0), Tclass._System.nat());
                ##n#1 := (if n#0 < 0 then 0 else n#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
                ##tail#1 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#1, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall((if n#0 < 0 then 0 else n#0), tail#0);
                ##_k#3 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#3, TORDINAL, $Heap);
                ##num#1 := _module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#1, Tclass._module.Number(), $Heap);
                assume _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0));
                assume _module.__default.S2N_k#canCall((if n#0 < 0 then 0 else n#0), tail#0)
                   && _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assume _module.__default.InfinitePath_k_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                if (n#0 < 0)
                {
                }
                else
                {
                }

                assert $Is((if n#0 < 0 then 0 else n#0), Tclass._System.nat());
                ##n#2 := (if n#0 < 0 then 0 else n#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
                ##tail#2 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#2, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall((if n#0 < 0 then 0 else n#0), tail#0);
                ##_k#4 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#4, TORDINAL, $Heap);
                ##r#3 := #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0)));
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#3, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.InfinitePath_h#canCall(_k#0, 
                  #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0))));
                assume _module.__default.S2N_k#canCall((if n#0 < 0 then 0 else n#0), tail#0)
                   && _module.__default.InfinitePath_h#canCall(_k#0, 
                    #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0))));
                // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assert {:subsumption 0} _module.__default.InfinitePath_k_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0))
                   ==> _module.__default.InfinitePath_h($LS($LS($LZ)), 
                    _k#0, 
                    #_module.CoOption.Some($Box(_module.__default.S2N_k($LS($LS($LZ)), (if n#0 < 0 then 0 else n#0), tail#0))));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assume ORD#IsNat(Lit(ORD#FromNat(1)));
                assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                ##p#2 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#2, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(tail#0);
                ##_k#1 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#1, TORDINAL, $Heap);
                ##r#2 := _module.__default.S2N($LS($LZ), tail#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#2, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.InfinitePath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.__default.S2N($LS($LZ), tail#0));
                assume _module.__default.S2N#canCall(tail#0)
                   && _module.__default.InfinitePath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.__default.S2N($LS($LZ), tail#0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assume _module.__default.InfinitePath_h($LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.__default.S2N($LS($LZ), tail#0));
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(622,24)
                // TrCallStmt: Before ProcessCallStmt
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                _k##1 := ORD#Minus(_k#0, ORD#FromNat(1));
                assume true;
                // ProcessCallStmt: CheckSubrange
                p##1 := p#1;
                if (n#0 < 0)
                {
                }
                else
                {
                }

                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is((if n#0 < 0 then 0 else n#0), Tclass._System.nat());
                n##0 := (if n#0 < 0 then 0 else n#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                tail##0 := tail#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call CoCall$$_module.__default.Path__Lemma2_k_k_h(_k##1, p##1, n##0, tail##0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(622,56)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                if (n#0 < 0)
                {
                }
                else
                {
                }

                assert $Is((if n#0 < 0 then 0 else n#0), Tclass._System.nat());
                ##n#0 := (if n#0 < 0 then 0 else n#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
                ##tail#0 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##tail#0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N_k#canCall((if n#0 < 0 then 0 else n#0), tail#0);
                ##_k#2 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#2, TORDINAL, $Heap);
                ##num#0 := _module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
                assume _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0));
                assume _module.__default.S2N_k#canCall((if n#0 < 0 then 0 else n#0), tail#0)
                   && _module.__default.InfinitePath_k_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.__default.S2N_k($LS($LZ), (if n#0 < 0 then 0 else n#0), tail#0));
                // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assert {:subsumption 0} _module.__default.InfinitePath_h($LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.__default.S2N($LS($LZ), tail#0))
                   ==> _module.__default.InfinitePath_k_h($LS($LS($LZ)), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.__default.S2N_k($LS($LS($LZ)), (if n#0 < 0 then 0 else n#0), tail#0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assume true;
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assume true;
                // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(624,21)
                // TrCallStmt: Before ProcessCallStmt
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
                assume true;
                // ProcessCallStmt: CheckSubrange
                p##0 := tail#0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call CoCall$$_module.__default.Path__Lemma2_k_h(_k##0, p##0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(624,26)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                ##p#1 := tail#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#1, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(tail#0);
                ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                ##r#1 := _module.__default.S2N($LS($LZ), tail#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.InfinitePath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.__default.S2N($LS($LZ), tail#0));
                assume _module.__default.S2N#canCall(tail#0)
                   && _module.__default.InfinitePath_h#canCall(ORD#Minus(_k#0, ORD#FromNat(1)), _module.__default.S2N($LS($LZ), tail#0));
                // ----- assert line3 <== line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(616,5)
                assert {:subsumption 0} Lit(true)
                   ==> _module.__default.InfinitePath_h($LS($LS($LZ)), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.__default.S2N($LS($LS($LZ)), tail#0));
                assume false;
            }

            assume true
               ==> _module.__default.InfinitePath_h($LS($LZ), _k#0, _module.__default.S2N($LS($LZ), p#1));
        }
        else if (p#1 == #_module.Stream.Nil())
        {
            assert false;
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(610,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, p#2: DatatypeType :: 
          $Is(p#2, Tclass._module.Stream(TInt))
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#2)
             ==> _module.__default.InfinitePath_h($LS($LZ), _k'#0, _module.__default.S2N($LS($LZ), p#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(610,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Path__Lemma2_k_k(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0), 
    n#0: int where LitInt(0) <= n#0, 
    tail#0: DatatypeType
       where $Is(tail#0, Tclass._module.Stream(TInt))
         && $IsAlloc(tail#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(tail#0));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Path__Lemma2_k_k(p#0: DatatypeType, n#0: int, tail#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##s#0: DatatypeType;
  var ##n#0: int;
  var ##tail#0: DatatypeType;
  var ##num#0: DatatypeType;

    // AddMethodImpl: Path_Lemma2'', CheckWellformed$$_module.__default.Path__Lemma2_k_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(629,15): initial state"} true;
    ##s#0 := p#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.IsNeverEndingStream#canCall(TInt, p#0);
    assume _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0);
    assert _module.Stream.Cons_q(p#0);
    assume $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), _module.Stream.tail(p#0), tail#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(631,23): post-state"} true;
    ##n#0 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    ##tail#0 := tail#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##tail#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.S2N_k#canCall(n#0, tail#0);
    ##num#0 := _module.__default.S2N_k($LS($LZ), n#0, tail#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##num#0, Tclass._module.Number(), $Heap);
    assume _module.__default.InfinitePath_k#canCall(_module.__default.S2N_k($LS($LZ), n#0, tail#0));
    assume _module.__default.InfinitePath_k($LS($LZ), _module.__default.S2N_k($LS($LZ), n#0, tail#0));
}



procedure Call$$_module.__default.Path__Lemma2_k_k(p#0: DatatypeType
       where $Is(p#0, Tclass._module.Stream(TInt))
         && $IsAlloc(p#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#0), 
    n#0: int where LitInt(0) <= n#0, 
    tail#0: DatatypeType
       where $Is(tail#0, Tclass._module.Stream(TInt))
         && $IsAlloc(tail#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(tail#0));
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0);
  requires $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), _module.Stream.tail(p#0), tail#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N_k#canCall(n#0, tail#0)
     && _module.__default.InfinitePath_k#canCall(_module.__default.S2N_k($LS($LZ), n#0, tail#0));
  ensures _module.__default.InfinitePath_k($LS($LS($LZ)), _module.__default.S2N_k($LS($LS($LZ)), n#0, tail#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, p#1, n#1, tail#1} CoCall$$_module.__default.Path__Lemma2_k_k_h(_k#0: Box, 
    p#1: DatatypeType
       where $Is(p#1, Tclass._module.Stream(TInt))
         && $IsAlloc(p#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#1), 
    n#1: int where LitInt(0) <= n#1, 
    tail#1: DatatypeType
       where $Is(tail#1, Tclass._module.Stream(TInt))
         && $IsAlloc(tail#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(tail#1));
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1);
  requires $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), _module.Stream.tail(p#1), tail#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N_k#canCall(n#1, tail#1)
     && _module.__default.InfinitePath_k_h#canCall(_k#0, _module.__default.S2N_k($LS($LZ), n#1, tail#1));
  ensures _module.__default.InfinitePath_k_h($LS($LS($LZ)), _k#0, _module.__default.S2N_k($LS($LS($LZ)), n#1, tail#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, p#1, n#1, tail#1} Impl$$_module.__default.Path__Lemma2_k_k_h(_k#0: Box, 
    p#1: DatatypeType
       where $Is(p#1, Tclass._module.Stream(TInt))
         && $IsAlloc(p#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(p#1), 
    n#1: int where LitInt(0) <= n#1, 
    tail#1: DatatypeType
       where $Is(tail#1, Tclass._module.Stream(TInt))
         && $IsAlloc(tail#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(tail#1))
   returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#1);
  requires $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), _module.Stream.tail(p#1), tail#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.S2N_k#canCall(n#1, tail#1)
     && _module.__default.InfinitePath_k_h#canCall(_k#0, _module.__default.S2N_k($LS($LZ), n#1, tail#1));
  ensures _module.__default.InfinitePath_k_h($LS($LS($LZ)), _k#0, _module.__default.S2N_k($LS($LS($LZ)), n#1, tail#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, p#1, n#1, tail#1} Impl$$_module.__default.Path__Lemma2_k_k_h(_k#0: Box, p#1: DatatypeType, n#1: int, tail#1: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _k##0: Box;
  var p##0: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Path_Lemma2''#, Impl$$_module.__default.Path__Lemma2_k_k_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(629,15): initial state"} true;
    assume $IsA#_module.Stream(p#1);
    assume $IsA#_module.Stream(tail#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#p0#0: DatatypeType, $ih#n0#0: int, $ih#tail0#0: DatatypeType :: 
      $Is($ih#p0#0, Tclass._module.Stream(TInt))
           && LitInt(0) <= $ih#n0#0
           && $Is($ih#tail0#0, Tclass._module.Stream(TInt))
           && 
          _module.__default.IsNeverEndingStream(TInt, $LS($LZ), $ih#p0#0)
           && $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), _module.Stream.tail($ih#p0#0), $ih#tail0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && 0 <= $ih#n0#0 && $ih#n0#0 < n#1))
         ==> _module.__default.InfinitePath_k_h($LS($LZ), $ih#_k0#0, _module.__default.S2N_k($LS($LZ), $ih#n0#0, $ih#tail0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(632,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(633,15)
        // TrCallStmt: Before ProcessCallStmt
        assert ORD#IsNat(Lit(ORD#FromNat(1)));
        assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
        assume true;
        // ProcessCallStmt: CheckSubrange
        _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
        assume true;
        // ProcessCallStmt: CheckSubrange
        p##0 := tail#1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call CoCall$$_module.__default.Path__Lemma2_k_h(_k##0, p##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(633,20)"} true;
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(629,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, p#2: DatatypeType, n#2: int, tail#2: DatatypeType :: 
          $Is(p#2, Tclass._module.Stream(TInt))
               && LitInt(0) <= n#2
               && $Is(tail#2, Tclass._module.Stream(TInt))
               && 
              ORD#Less(_k'#0, _k#0)
               && 
              _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#2)
               && $Eq#_module.Stream(TInt, TInt, $LS($LS($LZ)), _module.Stream.tail(p#2), tail#2)
             ==> _module.__default.InfinitePath_k_h($LS($LZ), _k'#0, _module.__default.S2N_k($LS($LZ), n#2, tail#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(629,15)"} true;
    }
}



procedure {:_induction r#0} CheckWellformed$$_module.__default.Path__Lemma3(r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#0));
  free requires 64 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction r#0} Call$$_module.__default.Path__Lemma3(r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.InfinitePath#canCall(r#0)
     && (_module.__default.InfinitePath($LS($LZ), r#0)
       ==> _module.__default.N2S#canCall(r#0)
         && _module.__default.IsNeverEndingStream#canCall(TInt, _module.__default.N2S($LS($LZ), r#0)));
  ensures _module.__default.InfinitePath($LS($LZ), r#0)
     ==> _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), _module.__default.N2S($LS($LS($LZ)), r#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction r#0} Impl$$_module.__default.Path__Lemma3(r#0: DatatypeType
       where $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
         && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap)
         && $IsA#_module.CoOption(r#0))
   returns ($_reverifyPost: bool);
  free requires 64 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.InfinitePath#canCall(r#0)
     && (_module.__default.InfinitePath($LS($LZ), r#0)
       ==> _module.__default.N2S#canCall(r#0)
         && _module.__default.IsNeverEndingStream#canCall(TInt, _module.__default.N2S($LS($LZ), r#0)));
  ensures _module.__default.InfinitePath($LS($LZ), r#0)
     ==> _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), _module.__default.N2S($LS($LS($LZ)), r#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction r#0} Impl$$_module.__default.Path__Lemma3(r#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var ##r#2: DatatypeType;
  var _mcc#0#0_0_0: DatatypeType;
  var num#0_0_0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var n##0_0_0: int;
  var num##0_0_0: DatatypeType;

    // AddMethodImpl: Path_Lemma3, Impl$$_module.__default.Path__Lemma3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(637,0): initial state"} true;
    assume $IsA#_module.CoOption(r#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#r0#0: DatatypeType :: 
      $Is($ih#r0#0, Tclass._module.CoOption(Tclass._module.Number()))
           && Lit(true)
           && false
         ==> 
        _module.__default.InfinitePath($LS($LZ), $ih#r0#0)
         ==> _module.__default.IsNeverEndingStream(TInt, $LS($LZ), _module.__default.N2S($LS($LZ), $ih#r0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(638,3)
    ##r#2 := r#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#2, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
    assume _module.__default.InfinitePath#canCall(r#0);
    assume _module.__default.InfinitePath#canCall(r#0);
    if (_module.__default.InfinitePath($LS($LZ), r#0))
    {
        assume true;
        havoc _mcc#0#0_0_0;
        if (r#0 == #_module.CoOption.Some($Box(_mcc#0#0_0_0)))
        {
            assume $Is(_mcc#0#0_0_0, Tclass._module.Number());
            havoc num#0_0_0;
            assume $Is(num#0_0_0, Tclass._module.Number())
               && $IsAlloc(num#0_0_0, Tclass._module.Number(), $Heap);
            assume let#0_0_0#0#0 == _mcc#0#0_0_0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.Number());
            assume num#0_0_0 == let#0_0_0#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(640,37)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(LitInt(0), Tclass._System.nat());
            n##0_0_0 := LitInt(0);
            assume true;
            // ProcessCallStmt: CheckSubrange
            num##0_0_0 := num#0_0_0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Path__Lemma3_k(n##0_0_0, num##0_0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(640,44)"} true;
        }
        else if (r#0 == #_module.CoOption.None())
        {
            assert false;
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



procedure CheckWellformed$$_module.__default.Path__Lemma3_k(n#0: int where LitInt(0) <= n#0, 
    num#0: DatatypeType
       where $Is(num#0, Tclass._module.Number())
         && $IsAlloc(num#0, Tclass._module.Number(), $Heap)
         && $IsA#_module.Number(num#0));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Path__Lemma3_k(n#0: int where LitInt(0) <= n#0, 
    num#0: DatatypeType
       where $Is(num#0, Tclass._module.Number())
         && $IsAlloc(num#0, Tclass._module.Number(), $Heap)
         && $IsA#_module.Number(num#0));
  // user-defined preconditions
  requires _module.__default.InfinitePath_k($LS($LS($LZ)), num#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S_k#canCall(n#0, num#0)
     && _module.__default.IsNeverEndingStream#canCall(TInt, _module.__default.N2S_k($LS($LZ), n#0, num#0));
  ensures _module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), _module.__default.N2S_k($LS($LS($LZ)), n#0, num#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, n#1, num#1} CoCall$$_module.__default.Path__Lemma3_k_h(_k#0: Box, 
    n#1: int where LitInt(0) <= n#1, 
    num#1: DatatypeType
       where $Is(num#1, Tclass._module.Number())
         && $IsAlloc(num#1, Tclass._module.Number(), $Heap)
         && $IsA#_module.Number(num#1));
  // user-defined preconditions
  requires _module.__default.InfinitePath_k($LS($LS($LZ)), num#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S_k#canCall(n#1, num#1)
     && _module.__default.IsNeverEndingStream_h#canCall(TInt, _k#0, _module.__default.N2S_k($LS($LZ), n#1, num#1));
  ensures _module.__default.IsNeverEndingStream_h(TInt, $LS($LS($LZ)), _k#0, _module.__default.N2S_k($LS($LS($LZ)), n#1, num#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, n#1, num#1} Impl$$_module.__default.Path__Lemma3_k_h(_k#0: Box, 
    n#1: int where LitInt(0) <= n#1, 
    num#1: DatatypeType
       where $Is(num#1, Tclass._module.Number())
         && $IsAlloc(num#1, Tclass._module.Number(), $Heap)
         && $IsA#_module.Number(num#1))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  // user-defined preconditions
  requires _module.__default.InfinitePath_k($LS($LS($LZ)), num#1);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.N2S_k#canCall(n#1, num#1)
     && _module.__default.IsNeverEndingStream_h#canCall(TInt, _k#0, _module.__default.N2S_k($LS($LZ), n#1, num#1));
  ensures _module.__default.IsNeverEndingStream_h(TInt, $LS($LS($LZ)), _k#0, _module.__default.N2S_k($LS($LS($LZ)), n#1, num#1));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, n#1, num#1} Impl$$_module.__default.Path__Lemma3_k_h(_k#0: Box, n#1: int, num#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#1#0: DatatypeType;
  var r#0: DatatypeType;
  var let#0_0_0#0#0: DatatypeType;
  var _k##0: Box;
  var n##0: int;
  var num##0: DatatypeType;
  var ##r#0: DatatypeType;
  var ##_k#0: Box;
  var ##s#1: DatatypeType;
  var ##r#1: DatatypeType;
  var ##_k#1: Box;
  var ##s#2: DatatypeType;
  var ##r#2: DatatypeType;
  var ##_k#2: Box;
  var ##s#3: DatatypeType;
  var ##r#3: DatatypeType;
  var ##_k#3: Box;
  var ##s#4: DatatypeType;
  var ##n#1: int;
  var ##num#2: DatatypeType;
  var ##_k#4: Box;
  var ##s#5: DatatypeType;
  var _mcc#0#0: DatatypeType;
  var next#0: DatatypeType;
  var let#0_1_0#0#0: DatatypeType;
  var _k##1: Box;
  var n##1: int;
  var num##1: DatatypeType;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: Path_Lemma3'#, Impl$$_module.__default.Path__Lemma3_k_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(644,15): initial state"} true;
    assume $IsA#_module.Number(num#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#n0#0: int, $ih#num0#0: DatatypeType :: 
      LitInt(0) <= $ih#n0#0
           && $Is($ih#num0#0, Tclass._module.Number())
           && _module.__default.InfinitePath_k($LS($LZ), $ih#num0#0)
           && (ORD#Less($ih#_k0#0, _k#0)
             || ($ih#_k0#0 == _k#0 && DtRank($ih#num0#0) < DtRank(num#1)))
         ==> _module.__default.IsNeverEndingStream_h(TInt, 
          $LS($LZ), 
          $ih#_k0#0, 
          _module.__default.N2S_k($LS($LZ), $ih#n0#0, $ih#num0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(648,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
        assume true;
        havoc _mcc#1#0;
        havoc _mcc#0#0;
        if (num#1 == #_module.Number.Succ(_mcc#0#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.Number())
               && $IsAlloc(_mcc#0#0, Tclass._module.Number(), $Heap);
            havoc next#0;
            assume $Is(next#0, Tclass._module.Number())
               && $IsAlloc(next#0, Tclass._module.Number(), $Heap);
            assume let#0_1_0#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_1_0#0#0, Tclass._module.Number());
            assume next#0 == let#0_1_0#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(661,24)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            _k##1 := _k#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#1 + 1, Tclass._System.nat());
            n##1 := n#1 + 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            num##1 := next#0;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert ORD#Less(_k##1, _k#0) || (_k##1 == _k#0 && DtRank(num##1) < DtRank(num#1));
            // ProcessCallStmt: Make the call
            call CoCall$$_module.__default.Path__Lemma3_k_h(_k##1, n##1, num##1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(661,36)"} true;
        }
        else if (num#1 == #_module.Number.Zero(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()))
               && $IsAlloc(_mcc#1#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            havoc r#0;
            assume $Is(r#0, Tclass._module.CoOption(Tclass._module.Number()))
               && $IsAlloc(r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
            assume let#0_0_0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0_0_0#0#0, Tclass._module.CoOption(Tclass._module.Number()));
            assume r#0 == let#0_0_0#0#0;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assume true;
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                ##r#3 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#3, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#0);
                ##_k#3 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#3, TORDINAL, $Heap);
                ##s#4 := #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#4, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.IsNeverEndingStream_h#canCall(TInt, 
                  _k#0, 
                  #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                assume _module.__default.N2S#canCall(r#0)
                   && _module.__default.IsNeverEndingStream_h#canCall(TInt, 
                    _k#0, 
                    #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assume _module.__default.IsNeverEndingStream_h(TInt, 
                  $LS($LZ), 
                  _k#0, 
                  #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                ##n#1 := n#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
                ##num#2 := num#1;
                // assume allocatedness for argument to function
                assume $IsAlloc(##num#2, Tclass._module.Number(), $Heap);
                assume _module.__default.N2S_k#canCall(n#1, num#1);
                ##_k#4 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#4, TORDINAL, $Heap);
                ##s#5 := _module.__default.N2S_k($LS($LZ), n#1, num#1);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#5, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.IsNeverEndingStream_h#canCall(TInt, _k#0, _module.__default.N2S_k($LS($LZ), n#1, num#1));
                assume _module.__default.N2S_k#canCall(n#1, num#1)
                   && _module.__default.IsNeverEndingStream_h#canCall(TInt, _k#0, _module.__default.N2S_k($LS($LZ), n#1, num#1));
                // ----- assert line0 <== line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assert {:subsumption 0} _module.__default.IsNeverEndingStream_h(TInt, 
                    $LS($LZ), 
                    _k#0, 
                    #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)))
                   ==> _module.__default.IsNeverEndingStream_h(TInt, $LS($LS($LZ)), _k#0, _module.__default.N2S_k($LS($LS($LZ)), n#1, num#1));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assume ORD#IsNat(Lit(ORD#FromNat(1)));
                assume ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                ##r#1 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#0);
                ##_k#1 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#1, TORDINAL, $Heap);
                ##s#2 := _module.__default.N2S($LS($LZ), r#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#2, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.IsNeverEndingStream_h#canCall(TInt, ORD#Minus(_k#0, ORD#FromNat(1)), _module.__default.N2S($LS($LZ), r#0));
                assume _module.__default.N2S#canCall(r#0)
                   && _module.__default.IsNeverEndingStream_h#canCall(TInt, ORD#Minus(_k#0, ORD#FromNat(1)), _module.__default.N2S($LS($LZ), r#0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assume _module.__default.IsNeverEndingStream_h(TInt, 
                  $LS($LZ), 
                  ORD#Minus(_k#0, ORD#FromNat(1)), 
                  _module.__default.N2S($LS($LZ), r#0));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                ##r#2 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#2, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#0);
                ##_k#2 := _k#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#2, TORDINAL, $Heap);
                ##s#3 := #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0));
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#3, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.IsNeverEndingStream_h#canCall(TInt, 
                  _k#0, 
                  #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                assume _module.__default.N2S#canCall(r#0)
                   && _module.__default.IsNeverEndingStream_h#canCall(TInt, 
                    _k#0, 
                    #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LZ), r#0)));
                // ----- assert line1 <== line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assert {:subsumption 0} _module.__default.IsNeverEndingStream_h(TInt, 
                    $LS($LZ), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.__default.N2S($LS($LZ), r#0))
                   ==> _module.__default.IsNeverEndingStream_h(TInt, 
                    $LS($LS($LZ)), 
                    _k#0, 
                    #_module.Stream.Cons($Box(n#1), _module.__default.N2S($LS($LS($LZ)), r#0)));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assume true;
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assume true;
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(657,23)
                // TrCallStmt: Before ProcessCallStmt
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                _k##0 := ORD#Minus(_k#0, ORD#FromNat(1));
                assume true;
                // ProcessCallStmt: CheckSubrange
                assert $Is(LitInt(0), Tclass._System.nat());
                n##0 := LitInt(0);
                assert _module.CoOption.Some_q(r#0);
                assume true;
                // ProcessCallStmt: CheckSubrange
                num##0 := $Unbox(_module.CoOption.get(r#0)): DatatypeType;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert ORD#Less(_k##0, _k#0) || (_k##0 == _k#0 && DtRank(num##0) < DtRank(num#1));
                // ProcessCallStmt: Make the call
                call CoCall$$_module.__default.Path__Lemma3_k_h(_k##0, n##0, num##0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(657,32)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assert ORD#IsNat(Lit(ORD#FromNat(1)));
                assert ORD#Offset(Lit(ORD#FromNat(1))) <= ORD#Offset(_k#0);
                ##r#0 := r#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#0);
                ##_k#0 := ORD#Minus(_k#0, ORD#FromNat(1));
                // assume allocatedness for argument to function
                assume $IsAlloc(##_k#0, TORDINAL, $Heap);
                ##s#1 := _module.__default.N2S($LS($LZ), r#0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.IsNeverEndingStream_h#canCall(TInt, ORD#Minus(_k#0, ORD#FromNat(1)), _module.__default.N2S($LS($LZ), r#0));
                assume _module.__default.N2S#canCall(r#0)
                   && _module.__default.IsNeverEndingStream_h#canCall(TInt, ORD#Minus(_k#0, ORD#FromNat(1)), _module.__default.N2S($LS($LZ), r#0));
                // ----- assert line2 <== line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(651,7)
                assert {:subsumption 0} Lit(true)
                   ==> _module.__default.IsNeverEndingStream_h(TInt, 
                    $LS($LS($LZ)), 
                    ORD#Minus(_k#0, ORD#FromNat(1)), 
                    _module.__default.N2S($LS($LS($LZ)), r#0));
                assume false;
            }

            assume true
               ==> _module.__default.IsNeverEndingStream_h(TInt, $LS($LZ), _k#0, _module.__default.N2S_k($LS($LZ), n#1, num#1));
        }
        else
        {
            assume false;
        }
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(644,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, n#2: int, num#2: DatatypeType :: 
          LitInt(0) <= n#2
               && $Is(num#2, Tclass._module.Number())
               && 
              ORD#Less(_k'#0, _k#0)
               && _module.__default.InfinitePath_k($LS($LZ), num#2)
             ==> _module.__default.IsNeverEndingStream_h(TInt, $LS($LZ), _k'#0, _module.__default.N2S_k($LS($LZ), n#2, num#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(644,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.Theorem2(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0));
  free requires 65 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Theorem2(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.HasFiniteHeight#canCall(t#0)
     && _module.__default.HasFiniteHeight__Alt#canCall(t#0);
  ensures _module.__default.HasFiniteHeight(t#0)
     <==> _module.__default.HasFiniteHeight__Alt(t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Theorem2(t#0: DatatypeType
       where $Is(t#0, Tclass._module.Tree())
         && $IsAlloc(t#0, Tclass._module.Tree(), $Heap)
         && $IsA#_module.Tree(t#0))
   returns ($_reverifyPost: bool);
  free requires 65 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.HasFiniteHeight#canCall(t#0)
     && _module.__default.HasFiniteHeight__Alt#canCall(t#0);
  ensures _module.__default.HasFiniteHeight(t#0)
     <==> _module.__default.HasFiniteHeight__Alt(t#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Theorem2(t#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##t#2: DatatypeType;
  var p#0_0: DatatypeType;
  var ##p#0_0_0_0: DatatypeType;
  var ##r#0_0_0_0: DatatypeType;
  var p##0_0_0_0: DatatypeType;
  var ##s#0_0_0_0: DatatypeType;
  var ##p#0_0_1_0: DatatypeType;
  var ##t#0_0_1_0: DatatypeType;
  var ##r#0_0_1_0: DatatypeType;
  var ##p#0_0_1_1: DatatypeType;
  var ##r#0_0_1_1: DatatypeType;
  var ##t#0_0_2_0: DatatypeType;
  var ##p#0_0_2_0: DatatypeType;
  var t##0_0_2_0: DatatypeType;
  var p##0_0_2_0: DatatypeType;
  var ##p#0_0_2_1: DatatypeType;
  var ##t#0_0_2_1: DatatypeType;
  var ##r#0_0_2_0: DatatypeType;
  var ##t#0_0_0: DatatypeType;
  var ##p#0_0_0: DatatypeType;
  var ##t#3: DatatypeType;
  var r#1_0: DatatypeType;
  var ##r#1_0_0_0: DatatypeType;
  var ##s#1_0_0_0: DatatypeType;
  var r##1_0_0_0: DatatypeType;
  var ##r#1_0_0_1: DatatypeType;
  var ##r#1_0_1_0: DatatypeType;
  var ##t#1_0_1_0: DatatypeType;
  var ##p#1_0_1_0: DatatypeType;
  var ##r#1_0_1_1: DatatypeType;
  var ##s#1_0_1_0: DatatypeType;
  var ##t#1_0_2_0: DatatypeType;
  var ##r#1_0_2_0: DatatypeType;
  var t##1_0_2_0: DatatypeType;
  var r##1_0_2_0: DatatypeType;
  var ##r#1_0_2_1: DatatypeType;
  var ##t#1_0_2_1: DatatypeType;
  var ##p#1_0_2_0: DatatypeType;
  var ##t#1_0_0: DatatypeType;
  var ##r#1_0_0: DatatypeType;

    // AddMethodImpl: Theorem2, Impl$$_module.__default.Theorem2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(667,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(668,3)
    ##t#2 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#2, Tclass._module.Tree(), $Heap);
    assume _module.__default.HasFiniteHeight__Alt#canCall(t#0);
    assume _module.__default.HasFiniteHeight__Alt#canCall(t#0);
    if (_module.__default.HasFiniteHeight__Alt(t#0))
    {
        // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(669,5)
        if (*)
        {
            // Assume Fuel Constant
            havoc p#0_0;
            assume $Is(p#0_0, Tclass._module.Stream(TInt));
            assume true;
            assume true;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                ##t#0_0_0 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#0_0_0, Tclass._module.Tree(), $Heap);
                ##p#0_0_0 := p#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0_0_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath#canCall(t#0, p#0_0);
                assume _module.__default.ValidPath#canCall(t#0, p#0_0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                ##t#0_0_2_0 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#0_0_2_0, Tclass._module.Tree(), $Heap);
                ##p#0_0_2_0 := p#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0_0_2_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath#canCall(t#0, p#0_0);
                assume _module.__default.ValidPath#canCall(t#0, p#0_0);
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                assume _module.__default.ValidPath($LS($LZ), t#0, p#0_0);
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(672,22)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                t##0_0_2_0 := t#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                p##0_0_2_0 := p#0_0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Path__Lemma0(t##0_0_2_0, p##0_0_2_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(672,27)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                ##p#0_0_2_1 := p#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0_0_2_1, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(p#0_0);
                ##t#0_0_2_1 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#0_0_2_1, Tclass._module.Tree(), $Heap);
                ##r#0_0_2_0 := _module.__default.S2N($LS($LZ), p#0_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#0_0_2_0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.ValidPath__Alt#canCall(t#0, _module.__default.S2N($LS($LZ), p#0_0));
                assume _module.__default.S2N#canCall(p#0_0)
                   && _module.__default.ValidPath__Alt#canCall(t#0, _module.__default.S2N($LS($LZ), p#0_0));
                // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                assert {:subsumption 0} _module.__default.ValidPath($LS($LZ), t#0, p#0_0)
                   ==> _module.__default.ValidPath__Alt($LS($LS($LZ)), t#0, _module.__default.S2N($LS($LS($LZ)), p#0_0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                ##p#0_0_1_0 := p#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0_0_1_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(p#0_0);
                ##t#0_0_1_0 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#0_0_1_0, Tclass._module.Tree(), $Heap);
                ##r#0_0_1_0 := _module.__default.S2N($LS($LZ), p#0_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#0_0_1_0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.ValidPath__Alt#canCall(t#0, _module.__default.S2N($LS($LZ), p#0_0));
                assume _module.__default.S2N#canCall(p#0_0)
                   && _module.__default.ValidPath__Alt#canCall(t#0, _module.__default.S2N($LS($LZ), p#0_0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                assume _module.__default.ValidPath__Alt($LS($LZ), t#0, _module.__default.S2N($LS($LZ), p#0_0));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                ##p#0_0_1_1 := p#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0_0_1_1, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(p#0_0);
                ##r#0_0_1_1 := _module.__default.S2N($LS($LZ), p#0_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#0_0_1_1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.InfinitePath#canCall(_module.__default.S2N($LS($LZ), p#0_0));
                assume _module.__default.S2N#canCall(p#0_0)
                   && _module.__default.InfinitePath#canCall(_module.__default.S2N($LS($LZ), p#0_0));
                // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                assert {:subsumption 0} _module.__default.ValidPath__Alt($LS($LZ), t#0, _module.__default.S2N($LS($LZ), p#0_0))
                   ==> !_module.__default.InfinitePath($LS($LS($LZ)), _module.__default.S2N($LS($LS($LZ)), p#0_0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                ##p#0_0_0_0 := p#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#0_0_0_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.S2N#canCall(p#0_0);
                ##r#0_0_0_0 := _module.__default.S2N($LS($LZ), p#0_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#0_0_0_0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.InfinitePath#canCall(_module.__default.S2N($LS($LZ), p#0_0));
                assume _module.__default.S2N#canCall(p#0_0)
                   && _module.__default.InfinitePath#canCall(_module.__default.S2N($LS($LZ), p#0_0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                assume !_module.__default.InfinitePath($LS($LZ), _module.__default.S2N($LS($LZ), p#0_0));
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(676,22)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                p##0_0_0_0 := p#0_0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Path__Lemma2(p##0_0_0_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(676,24)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                ##s#0_0_0_0 := p#0_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#0_0_0_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.IsNeverEndingStream#canCall(TInt, p#0_0);
                assume _module.__default.IsNeverEndingStream#canCall(TInt, p#0_0);
                // ----- assert line2 ==> line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(670,7)
                assert {:subsumption 0} !_module.__default.InfinitePath($LS($LZ), _module.__default.S2N($LS($LZ), p#0_0))
                   ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0_0);
                assume false;
            }

            assume _module.__default.ValidPath($LS($LZ), t#0, p#0_0)
               ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0_0);
            assert _module.__default.ValidPath($LS($LZ), t#0, p#0_0)
               ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), p#0_0);
            assume false;
        }
        else
        {
            assume (forall p#0_1: DatatypeType :: 
              { _module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0_1) } 
                { _module.__default.ValidPath($LS($LZ), t#0, p#0_1) } 
              $Is(p#0_1, Tclass._module.Stream(TInt)) && Lit(true)
                 ==> 
                _module.__default.ValidPath($LS($LZ), t#0, p#0_1)
                 ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), p#0_1));
        }

        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(679,4)"} true;
    }
    else
    {
    }

    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(681,3)
    ##t#3 := t#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##t#3, Tclass._module.Tree(), $Heap);
    assume _module.__default.HasFiniteHeight#canCall(t#0);
    assume _module.__default.HasFiniteHeight#canCall(t#0);
    if (_module.__default.HasFiniteHeight(t#0))
    {
        // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(682,5)
        if (*)
        {
            // Assume Fuel Constant
            havoc r#1_0;
            assume $Is(r#1_0, Tclass._module.CoOption(Tclass._module.Number()));
            assume true;
            assume true;
            // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
            // Assume Fuel Constant
            if (*)
            {
                // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                ##t#1_0_0 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#1_0_0, Tclass._module.Tree(), $Heap);
                ##r#1_0_0 := r#1_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1_0_0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.ValidPath__Alt#canCall(t#0, r#1_0);
                assume _module.__default.ValidPath__Alt#canCall(t#0, r#1_0);
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                ##t#1_0_2_0 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#1_0_2_0, Tclass._module.Tree(), $Heap);
                ##r#1_0_2_0 := r#1_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1_0_2_0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.ValidPath__Alt#canCall(t#0, r#1_0);
                assume _module.__default.ValidPath__Alt#canCall(t#0, r#1_0);
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                assume _module.__default.ValidPath__Alt($LS($LZ), t#0, r#1_0);
                // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(685,22)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                t##1_0_2_0 := t#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                r##1_0_2_0 := r#1_0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Path__Lemma1(t##1_0_2_0, r##1_0_2_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(685,27)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                ##r#1_0_2_1 := r#1_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1_0_2_1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#1_0);
                ##t#1_0_2_1 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#1_0_2_1, Tclass._module.Tree(), $Heap);
                ##p#1_0_2_0 := _module.__default.N2S($LS($LZ), r#1_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#1_0_2_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath#canCall(t#0, _module.__default.N2S($LS($LZ), r#1_0));
                assume _module.__default.N2S#canCall(r#1_0)
                   && _module.__default.ValidPath#canCall(t#0, _module.__default.N2S($LS($LZ), r#1_0));
                // ----- assert line0 ==> line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                assert {:subsumption 0} _module.__default.ValidPath__Alt($LS($LZ), t#0, r#1_0)
                   ==> _module.__default.ValidPath($LS($LS($LZ)), t#0, _module.__default.N2S($LS($LS($LZ)), r#1_0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                ##r#1_0_1_0 := r#1_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1_0_1_0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#1_0);
                ##t#1_0_1_0 := t#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##t#1_0_1_0, Tclass._module.Tree(), $Heap);
                ##p#1_0_1_0 := _module.__default.N2S($LS($LZ), r#1_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##p#1_0_1_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.ValidPath#canCall(t#0, _module.__default.N2S($LS($LZ), r#1_0));
                assume _module.__default.N2S#canCall(r#1_0)
                   && _module.__default.ValidPath#canCall(t#0, _module.__default.N2S($LS($LZ), r#1_0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                assume _module.__default.ValidPath($LS($LZ), t#0, _module.__default.N2S($LS($LZ), r#1_0));
                // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                ##r#1_0_1_1 := r#1_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1_0_1_1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#1_0);
                ##s#1_0_1_0 := _module.__default.N2S($LS($LZ), r#1_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1_0_1_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.IsNeverEndingStream#canCall(TInt, _module.__default.N2S($LS($LZ), r#1_0));
                assume _module.__default.N2S#canCall(r#1_0)
                   && _module.__default.IsNeverEndingStream#canCall(TInt, _module.__default.N2S($LS($LZ), r#1_0));
                // ----- assert line1 ==> line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                assert {:subsumption 0} _module.__default.ValidPath($LS($LZ), t#0, _module.__default.N2S($LS($LZ), r#1_0))
                   ==> !_module.__default.IsNeverEndingStream(TInt, $LS($LS($LZ)), _module.__default.N2S($LS($LS($LZ)), r#1_0));
                assume false;
            }
            else if (*)
            {
                // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                ##r#1_0_0_0 := r#1_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1_0_0_0, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.N2S#canCall(r#1_0);
                ##s#1_0_0_0 := _module.__default.N2S($LS($LZ), r#1_0);
                // assume allocatedness for argument to function
                assume $IsAlloc(##s#1_0_0_0, Tclass._module.Stream(TInt), $Heap);
                assume _module.__default.IsNeverEndingStream#canCall(TInt, _module.__default.N2S($LS($LZ), r#1_0));
                assume _module.__default.N2S#canCall(r#1_0)
                   && _module.__default.IsNeverEndingStream#canCall(TInt, _module.__default.N2S($LS($LZ), r#1_0));
                // ----- assume lhs ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                assume !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), _module.__default.N2S($LS($LZ), r#1_0));
                // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(689,22)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                // ProcessCallStmt: CheckSubrange
                r##1_0_0_0 := r#1_0;
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$_module.__default.Path__Lemma3(r##1_0_0_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(689,24)"} true;
                // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                ##r#1_0_0_1 := r#1_0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1_0_0_1, Tclass._module.CoOption(Tclass._module.Number()), $Heap);
                assume _module.__default.InfinitePath#canCall(r#1_0);
                assume _module.__default.InfinitePath#canCall(r#1_0);
                // ----- assert line2 ==> line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(683,7)
                assert {:subsumption 0} !_module.__default.IsNeverEndingStream(TInt, $LS($LZ), _module.__default.N2S($LS($LZ), r#1_0))
                   ==> !_module.__default.InfinitePath($LS($LS($LZ)), r#1_0);
                assume false;
            }

            assume _module.__default.ValidPath__Alt($LS($LZ), t#0, r#1_0)
               ==> !_module.__default.InfinitePath($LS($LZ), r#1_0);
            assert _module.__default.ValidPath__Alt($LS($LZ), t#0, r#1_0)
               ==> !_module.__default.InfinitePath($LS($LS($LZ)), r#1_0);
            assume false;
        }
        else
        {
            assume (forall r#1_1: DatatypeType :: 
              { _module.__default.InfinitePath($LS($LZ), r#1_1) } 
                { _module.__default.ValidPath__Alt($LS($LZ), t#0, r#1_1) } 
              $Is(r#1_1, Tclass._module.CoOption(Tclass._module.Number())) && Lit(true)
                 ==> 
                _module.__default.ValidPath__Alt($LS($LZ), t#0, r#1_1)
                 ==> !_module.__default.InfinitePath($LS($LZ), r#1_1));
        }

        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/InfiniteTrees.dfy(692,4)"} true;
    }
    else
    {
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

const unique tytagFamily$Tree: TyTagFamily;

const unique tytagFamily$CoOption: TyTagFamily;

const unique tytagFamily$Number: TyTagFamily;

const unique tytagFamily$InfPath: TyTagFamily;

const unique tytagFamily$FinPath: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
