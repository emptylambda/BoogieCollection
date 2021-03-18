// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy -print:./UnionFind.bpl

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

const unique class.M3.UnionFind?: ClassName;

function Tclass.M3.UnionFind?() : Ty;

const unique Tagclass.M3.UnionFind?: TyTag;

// Tclass.M3.UnionFind? Tag
axiom Tag(Tclass.M3.UnionFind?()) == Tagclass.M3.UnionFind?
   && TagFamily(Tclass.M3.UnionFind?()) == tytagFamily$UnionFind;

// Box/unbox axiom for Tclass.M3.UnionFind?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M3.UnionFind?()) } 
  $IsBox(bx, Tclass.M3.UnionFind?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M3.UnionFind?()));

// UnionFind: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M3.UnionFind?()) } 
  $Is($o, Tclass.M3.UnionFind?())
     <==> $o == null || dtype($o) == Tclass.M3.UnionFind?());

// UnionFind: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M3.UnionFind?(), $h) } 
  $IsAlloc($o, Tclass.M3.UnionFind?(), $h) <==> $o == null || read($h, $o, alloc));

function Tclass.M3.UnionFind() : Ty;

const unique Tagclass.M3.UnionFind: TyTag;

// Tclass.M3.UnionFind Tag
axiom Tag(Tclass.M3.UnionFind()) == Tagclass.M3.UnionFind
   && TagFamily(Tclass.M3.UnionFind()) == tytagFamily$UnionFind;

// Box/unbox axiom for Tclass.M3.UnionFind
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M3.UnionFind()) } 
  $IsBox(bx, Tclass.M3.UnionFind())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M3.UnionFind()));

function Tclass.M3.Element() : Ty;

const unique Tagclass.M3.Element: TyTag;

// Tclass.M3.Element Tag
axiom Tag(Tclass.M3.Element()) == Tagclass.M3.Element
   && TagFamily(Tclass.M3.Element()) == tytagFamily$Element;

// Box/unbox axiom for Tclass.M3.Element
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M3.Element()) } 
  $IsBox(bx, Tclass.M3.Element())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M3.Element()));

procedure CheckWellformed$$M3.UnionFind.Join(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



axiom FDim(M3.UnionFind.Repr) == 0
   && FieldOfDecl(class.M3.UnionFind?, field$Repr) == M3.UnionFind.Repr
   && $IsGhostField(M3.UnionFind.Repr);

axiom FDim(M3.UnionFind.M) == 0
   && FieldOfDecl(class.M3.UnionFind?, field$M) == M3.UnionFind.M
   && $IsGhostField(M3.UnionFind.M);

function Tclass.M3.Element?() : Ty;

const unique Tagclass.M3.Element?: TyTag;

// Tclass.M3.Element? Tag
axiom Tag(Tclass.M3.Element?()) == Tagclass.M3.Element?
   && TagFamily(Tclass.M3.Element?()) == tytagFamily$Element;

// Box/unbox axiom for Tclass.M3.Element?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M3.Element?()) } 
  $IsBox(bx, Tclass.M3.Element?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M3.Element?()));

implementation CheckWellformed$$M3.UnionFind.Join(this: ref, r0#0: ref, r1#0: ref) returns (r#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var e#0: ref;

    // AddMethodImpl: Join, CheckWellformed$$M3.UnionFind.Join
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, M3.UnionFind.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](110,11): initial state"} true;
    assume M3.UnionFind.Valid#canCall($Heap, this);
    assume M3.UnionFind.Valid($Heap, this);
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(r0#0)];
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(r1#0)];
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(r0#0)];
    assume $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(r0#0)]): ref == r0#0;
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(r1#0)];
    assume $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(r1#0)]): ref == r1#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o]
           || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
    assume $HeapSucc(old($Heap), $Heap);
    havoc r#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2](110,11): post-state"} true;
    assume M3.UnionFind.Valid#canCall($Heap, this);
    assume M3.UnionFind.Valid($Heap, this);
    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
    assume (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
           && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
    if (*)
    {
        assume r#0 == r0#0;
    }
    else
    {
        assume r#0 != r0#0;
        assume r#0 == r1#0;
    }

    // Begin Comprehension WF check
    havoc e#0;
    if ($Is(e#0, Tclass.M3.Element?()))
    {
        assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
        if (Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)])
        {
            assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
            assert Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)];
            if ($Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)]): ref
               != r0#0)
            {
                assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                assert Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)];
            }

            if ($Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)]): ref
                 == r0#0
               || $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)]): ref
                 == r1#0)
            {
            }
            else
            {
                assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                assert Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)];
            }
        }
    }

    // End Comprehension WF check
    assume Map#Equal(read($Heap, this, M3.UnionFind.M), 
      Map#Glue((lambda $w#0: Box :: 
          $Is($Unbox($w#0): ref, Tclass.M3.Element?())
             && Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$w#0]), 
        (lambda $w#0: Box :: 
          $Box((if $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#0]): ref == r0#0
                 || $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#0]): ref == r1#0
               then r#0
               else $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#0]): ref))), 
        TMap(Tclass.M3.Element?(), Tclass.M3.Element?())));
}



axiom FDim(M3.Element.c) == 0
   && FieldOfDecl(class.M3.Element?, field$c) == M3.Element.c
   && !$IsGhostField(M3.Element.c);

procedure Call$$M3.UnionFind.Join(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap));
  // user-defined preconditions
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#2: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]): ref } 
            $Is(e#2, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#3: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)] } 
            $Is(e#3, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#4: ref :: 
            { read($Heap, e#4, M3.Element.c) } 
            $Is(e#4, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
                 && M3.Contents.Link_q(read($Heap, e#4, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#4, M3.Element.c)))]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#5: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)] } 
            $Is(e#5, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref, 
                        M3.Element.c)), 
                    e#5, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(r0#0)];
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(r1#0)];
  requires $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(r0#0)]): ref == r0#0;
  requires $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(r1#0)]): ref == r1#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  free ensures M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures r#0 == r0#0 || r#0 == r1#0;
  free ensures true;
  ensures Map#Equal(read($Heap, this, M3.UnionFind.M), 
    Map#Glue((lambda $w#1: Box :: 
        $Is($Unbox($w#1): ref, Tclass.M3.Element?())
           && Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$w#1]), 
      (lambda $w#1: Box :: 
        $Box((if $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#1]): ref == r0#0
               || $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#1]): ref == r1#0
             then r#0
             else $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#1]): ref))), 
      TMap(Tclass.M3.Element?(), Tclass.M3.Element?())));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$M3.UnionFind.Join(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap))
   returns (defass#r#0: bool, 
    r#0: ref
       where defass#r#0
         ==> $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(r0#0)];
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(r1#0)];
  requires $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(r0#0)]): ref == r0#0;
  requires $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(r1#0)]): ref == r1#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  ensures M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  ensures M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  ensures M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  ensures M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#14: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]): ref } 
            $Is(e#14, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]]));
  ensures M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#15: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#15)] } 
            $Is(e#15, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]): ref));
  ensures M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#16: ref :: 
            { read($Heap, e#16, M3.Element.c) } 
            $Is(e#16, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]
                 && M3.Contents.Link_q(read($Heap, e#16, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#16, M3.Element.c)))]));
  ensures M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#17: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#17)] } 
            $Is(e#17, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]): ref, 
                        M3.Element.c)), 
                    e#17, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures r#0 == r0#0 || r#0 == r1#0;
  free ensures true;
  ensures Map#Equal(read($Heap, this, M3.UnionFind.M), 
    Map#Glue((lambda $w#2: Box :: 
        $Is($Unbox($w#2): ref, Tclass.M3.Element?())
           && Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$w#2]), 
      (lambda $w#2: Box :: 
        $Box((if $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#2]): ref == r0#0
               || $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#2]): ref == r1#0
             then r#0
             else $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#2]): ref))), 
      TMap(Tclass.M3.Element?(), Tclass.M3.Element?())));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function Tclass.M3.Contents() : Ty;

const unique Tagclass.M3.Contents: TyTag;

// Tclass.M3.Contents Tag
axiom Tag(Tclass.M3.Contents()) == Tagclass.M3.Contents
   && TagFamily(Tclass.M3.Contents()) == tytagFamily$Contents;

// Box/unbox axiom for Tclass.M3.Contents
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M3.Contents()) } 
  $IsBox(bx, Tclass.M3.Contents())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.M3.Contents()));

implementation Impl$$M3.UnionFind.Join(this: ref, r0#0: ref, r1#0: ref)
   returns (defass#r#0: bool, r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var m##0_0: Map Box Box;
  var n##0_0: Map Box Box;
  var e#0_0: ref;
  var $rhs#1_0: DatatypeType where $Is($rhs#1_0, Tclass.M3.Contents());
  var $rhs#1_1: Map Box Box
     where $Is($rhs#1_1, TMap(Tclass.M3.Element(), Tclass.M3.Element()));
  var e#1_0: ref;
  var e#1_2: ref;
  var r0##1_0: ref;
  var r1##1_0: ref;
  var C##1_0: Map Box Box;
  var C'##1_0: Map Box Box;
  var ##d#1_0: int;
  var ##e#1_0: ref;
  var ##r#1_0: ref;
  var ##C#1_0: Map Box Box;
  var $rhs#2_0: DatatypeType where $Is($rhs#2_0, Tclass.M3.Contents());
  var $rhs#2_1: Map Box Box
     where $Is($rhs#2_1, TMap(Tclass.M3.Element(), Tclass.M3.Element()));
  var e#2_0: ref;
  var e#2_2: ref;
  var r0##2_0: ref;
  var r1##2_0: ref;
  var C##2_0: Map Box Box;
  var C'##2_0: Map Box Box;
  var ##d#2_0: int;
  var ##e#2_0: ref;
  var ##r#2_0: ref;
  var ##C#2_0: Map Box Box;
  var $rhs#0: DatatypeType where $Is($rhs#0, Tclass.M3.Contents());
  var $rhs#1: DatatypeType where $Is($rhs#1, Tclass.M3.Contents());
  var $rhs#2: Map Box Box
     where $Is($rhs#2, TMap(Tclass.M3.Element(), Tclass.M3.Element()));
  var e#18: ref;
  var e#20: ref;
  var r0##0: ref;
  var r1##0: ref;
  var C##0: Map Box Box;
  var C'##0: Map Box Box;
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#0: Map Box Box;

    // AddMethodImpl: Join, Impl$$M3.UnionFind.Join
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, M3.UnionFind.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(208,4): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(209,7)
    assume true;
    if (r0#0 == r1#0)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(210,11)
        assume true;
        assume true;
        r#0 := r0#0;
        defass#r#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(210,15)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(211,18)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        m##0_0 := read($Heap, this, M3.UnionFind.M);
        // Begin Comprehension WF check
        havoc e#0_0;
        if ($Is(e#0_0, Tclass.M3.Element?()))
        {
            if (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0_0)])
            {
                assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0_0)];
                if ($Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0_0)]): ref
                   != r0#0)
                {
                    assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0_0)];
                }

                if ($Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0_0)]): ref
                     == r0#0
                   || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0_0)]): ref
                     == r1#0)
                {
                    assert defass#r#0;
                }
                else
                {
                    assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0_0)];
                }
            }
        }

        // End Comprehension WF check
        assume true;
        // ProcessCallStmt: CheckSubrange
        n##0_0 := Map#Glue((lambda $w#0_0: Box :: 
            $Is($Unbox($w#0_0): ref, Tclass.M3.Element?())
               && Map#Domain(read($Heap, this, M3.UnionFind.M))[$w#0_0]), 
          (lambda $w#0_0: Box :: 
            $Box((if $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#0_0]): ref == r0#0
                   || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#0_0]): ref == r1#0
                 then r#0
                 else $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#0_0]): ref))), 
          TMap(Tclass.M3.Element?(), Tclass.M3.Element?()));
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.__default.MapsEqual(Tclass.M3.Element?(), m##0_0, n##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(211,84)"} true;
        // ----- return statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(212,9)
        assert defass#r#0;
        return;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(213,14)
        assert r0#0 != null;
        assert M3.Contents.Root_q(read($Heap, r0#0, M3.Element.c));
        assert r1#0 != null;
        assert M3.Contents.Root_q(read($Heap, r1#0, M3.Element.c));
        assume true;
        if (M3.Contents.depth(read($Heap, r0#0, M3.Element.c))
           < M3.Contents.depth(read($Heap, r1#0, M3.Element.c)))
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(214,14)
            assert r0#0 != null;
            assume true;
            assert $_Frame[r0#0, M3.Element.c];
            assume true;
            $rhs#1_0 := #M3.Contents.Link(r1#0);
            $Heap := update($Heap, r0#0, M3.Element.c, $rhs#1_0);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(214,24)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(215,11)
            assume true;
            assume true;
            r#0 := r1#0;
            defass#r#0 := true;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(215,15)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(216,11)
            assume true;
            assert $_Frame[this, M3.UnionFind.M];
            // Begin Comprehension WF check
            havoc e#1_0;
            if ($Is(e#1_0, Tclass.M3.Element()))
            {
                if (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1_0)])
                {
                    assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1_0)];
                    if ($Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_0)]): ref
                       != r0#0)
                    {
                        assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1_0)];
                    }

                    if ($Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_0)]): ref
                         == r0#0
                       || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_0)]): ref
                         == r1#0)
                    {
                        assert defass#r#0;
                    }
                    else
                    {
                        assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1_0)];
                    }
                }
            }

            // End Comprehension WF check
            assume true;
            assert $Is(Map#Glue((lambda $w#1_0: Box :: 
                  $Is($Unbox($w#1_0): ref, Tclass.M3.Element())
                     && Map#Domain(read($Heap, this, M3.UnionFind.M))[$w#1_0]), 
                (lambda $w#1_0: Box :: 
                  $Box((if $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#1_0]): ref == r0#0
                         || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#1_0]): ref == r1#0
                       then r#0
                       else $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#1_0]): ref))), 
                TMap(Tclass.M3.Element(), Tclass.M3.Element?())), 
              TMap(Tclass.M3.Element(), Tclass.M3.Element()));
            $rhs#1_1 := Map#Glue((lambda $w#1_0: Box :: 
                $Is($Unbox($w#1_0): ref, Tclass.M3.Element())
                   && Map#Domain(read($Heap, this, M3.UnionFind.M))[$w#1_0]), 
              (lambda $w#1_0: Box :: 
                $Box((if $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#1_0]): ref == r0#0
                       || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#1_0]): ref == r1#0
                     then r#0
                     else $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#1_0]): ref))), 
              TMap(Tclass.M3.Element(), Tclass.M3.Element?()));
            $Heap := update($Heap, this, M3.UnionFind.M, $rhs#1_1);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(216,75)"} true;
            // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(217,9)
            if (*)
            {
                // Assume Fuel Constant
                havoc e#1_2;
                assume $Is(e#1_2, Tclass.M3.Element());
                assert {:subsumption 0} (forall f#1_0: ref :: 
                  { read($Heap, f#1_0, M3.Element.c) } 
                  $Is(f#1_0, Tclass.M3.Element())
                     ==> 
                    Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#1_0)]
                       && M3.Contents.Link_q(read($Heap, f#1_0, M3.Element.c))
                     ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#1_0, M3.Element.c)))]);
                assume M3.UnionFind.Collect#canCall($Heap, this);
                assume M3.UnionFind.Collect#canCall($Heap, this);
                assume Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#1_2)];
                // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(220,32)
                // TrCallStmt: Before ProcessCallStmt
                assume true;
                assume true;
                // ProcessCallStmt: CheckSubrange
                r0##1_0 := r0#0;
                assume true;
                // ProcessCallStmt: CheckSubrange
                r1##1_0 := r1#0;
                assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                assert {:subsumption 0} (forall f#1_1: ref :: 
                  { read(old($Heap), f#1_1, M3.Element.c) } 
                  $Is(f#1_1, Tclass.M3.Element())
                     ==> 
                    Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#1_1)]
                       && M3.Contents.Link_q(read(old($Heap), f#1_1, M3.Element.c))
                     ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#1_1, M3.Element.c)))]);
                assume (forall f#1_1: ref :: 
                  { read(old($Heap), f#1_1, M3.Element.c) } 
                  $Is(f#1_1, Tclass.M3.Element())
                     ==> 
                    Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#1_1)]
                       && M3.Contents.Link_q(read(old($Heap), f#1_1, M3.Element.c))
                     ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#1_1, M3.Element.c)))]);
                assume M3.UnionFind.Collect#canCall(old($Heap), this);
                assume M3.UnionFind.Collect#canCall(old($Heap), this);
                // ProcessCallStmt: CheckSubrange
                C##1_0 := M3.UnionFind.Collect(old($Heap), this);
                assert {:subsumption 0} (forall f#1_2: ref :: 
                  { read($Heap, f#1_2, M3.Element.c) } 
                  $Is(f#1_2, Tclass.M3.Element())
                     ==> 
                    Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#1_2)]
                       && M3.Contents.Link_q(read($Heap, f#1_2, M3.Element.c))
                     ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#1_2, M3.Element.c)))]);
                assume (forall f#1_2: ref :: 
                  { read($Heap, f#1_2, M3.Element.c) } 
                  $Is(f#1_2, Tclass.M3.Element())
                     ==> 
                    Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#1_2)]
                       && M3.Contents.Link_q(read($Heap, f#1_2, M3.Element.c))
                     ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#1_2, M3.Element.c)))]);
                assume M3.UnionFind.Collect#canCall($Heap, this);
                assume M3.UnionFind.Collect#canCall($Heap, this);
                // ProcessCallStmt: CheckSubrange
                C'##1_0 := M3.UnionFind.Collect($Heap, this);
                assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                // ProcessCallStmt: Make the call
                call Call$$M3.UnionFind.JoinMaintainsReaches0(this, r0##1_0, r1##1_0, C##1_0, C'##1_0);
                // TrCallStmt: After ProcessCallStmt
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(220,66)"} true;
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(221,11)
                assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                assert {:subsumption 0} Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)];
                assert {:subsumption 0} $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref
                   != null;
                assert $IsAlloc($Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                  Tclass.M3.Element(), 
                  old($Heap));
                assert M3.Contents.Root_q(read(old($Heap), 
                    $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                    M3.Element.c));
                assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                assert {:subsumption 0} Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)];
                assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                assert {:subsumption 0} (forall f#1_3: ref :: 
                  { read(old($Heap), f#1_3, M3.Element.c) } 
                  $Is(f#1_3, Tclass.M3.Element())
                     ==> 
                    Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#1_3)]
                       && M3.Contents.Link_q(read(old($Heap), f#1_3, M3.Element.c))
                     ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#1_3, M3.Element.c)))]);
                assume M3.UnionFind.Collect#canCall(old($Heap), this);
                ##d#1_0 := M3.Contents.depth(read(old($Heap), 
                    $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                    M3.Element.c));
                // assume allocatedness for argument to function
                assume $IsAlloc(##d#1_0, Tclass._System.nat(), $Heap);
                ##e#1_0 := e#1_2;
                // assume allocatedness for argument to function
                assume $IsAlloc(##e#1_0, Tclass.M3.Element(), $Heap);
                ##r#1_0 := $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref;
                // assume allocatedness for argument to function
                assume $IsAlloc(##r#1_0, Tclass.M3.Element(), $Heap);
                ##C#1_0 := M3.UnionFind.Collect(old($Heap), this);
                // assume allocatedness for argument to function
                assume $IsAlloc(##C#1_0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
                assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#1_0)
                   ==> M3.__default.GoodCMap(##C#1_0)
                     || (forall f#1_4: ref :: 
                      { $Unbox(Map#Elements(##C#1_0)[$Box(f#1_4)]): DatatypeType } 
                      $Is(f#1_4, Tclass.M3.Element?())
                         ==> 
                        Map#Domain(##C#1_0)[$Box(f#1_4)]
                           && M3.Contents.Link_q($Unbox(Map#Elements(##C#1_0)[$Box(f#1_4)]): DatatypeType)
                         ==> Map#Domain(##C#1_0)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#1_0)[$Box(f#1_4)]): DatatypeType))]);
                assert {:subsumption 0} Map#Domain(##C#1_0)[$Box(##e#1_0)];
                assume M3.UnionFind.Reaches#canCall(this, 
                  M3.Contents.depth(read(old($Heap), 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                      M3.Element.c)), 
                  e#1_2, 
                  $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                  M3.UnionFind.Collect(old($Heap), this));
                assume M3.UnionFind.Collect#canCall(old($Heap), this)
                   && M3.UnionFind.Reaches#canCall(this, 
                    M3.Contents.depth(read(old($Heap), 
                        $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                        M3.Element.c)), 
                    e#1_2, 
                    $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                    M3.UnionFind.Collect(old($Heap), this));
                assert {:subsumption 0} M3.UnionFind.Reaches($LS($LS($LZ)), 
                  this, 
                  M3.Contents.depth(read(old($Heap), 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                      M3.Element.c)), 
                  e#1_2, 
                  $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                  M3.UnionFind.Collect(old($Heap), this));
                assume M3.UnionFind.Reaches($LS($LZ), 
                  this, 
                  M3.Contents.depth(read(old($Heap), 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                      M3.Element.c)), 
                  e#1_2, 
                  $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                  M3.UnionFind.Collect(old($Heap), this));
                assert M3.Contents.Root_q(read($Heap, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                    M3.Element.c));
                assert M3.UnionFind.Reaches($LS($LS($LZ)), 
                  this, 
                  M3.Contents.depth(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                      M3.Element.c)), 
                  e#1_2, 
                  $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_2)]): ref, 
                  M3.UnionFind.Collect($Heap, this));
                assume false;
            }
            else
            {
                assume (forall e#1_3: ref :: 
                  { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_3)]): ref } 
                    { Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#1_3)] } 
                  $Is(e#1_3, Tclass.M3.Element())
                       && Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#1_3)]
                     ==> M3.Contents.Root_q(read($Heap, 
                          $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_3)]): ref, 
                          M3.Element.c))
                       && M3.UnionFind.Reaches($LS($LZ), 
                        this, 
                        M3.Contents.depth(read($Heap, 
                            $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_3)]): ref, 
                            M3.Element.c)), 
                        e#1_3, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1_3)]): ref, 
                        M3.UnionFind.Collect($Heap, this)));
            }

            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(222,8)"} true;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(223,14)
            assert r1#0 != null;
            assert M3.Contents.Root_q(read($Heap, r1#0, M3.Element.c));
            assert r0#0 != null;
            assert M3.Contents.Root_q(read($Heap, r0#0, M3.Element.c));
            assume true;
            if (M3.Contents.depth(read($Heap, r1#0, M3.Element.c))
               < M3.Contents.depth(read($Heap, r0#0, M3.Element.c)))
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(224,14)
                assert r1#0 != null;
                assume true;
                assert $_Frame[r1#0, M3.Element.c];
                assume true;
                $rhs#2_0 := #M3.Contents.Link(r0#0);
                $Heap := update($Heap, r1#0, M3.Element.c, $rhs#2_0);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(224,24)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(225,11)
                assume true;
                assume true;
                r#0 := r0#0;
                defass#r#0 := true;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(225,15)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(226,11)
                assume true;
                assert $_Frame[this, M3.UnionFind.M];
                // Begin Comprehension WF check
                havoc e#2_0;
                if ($Is(e#2_0, Tclass.M3.Element()))
                {
                    if (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2_0)])
                    {
                        assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2_0)];
                        if ($Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_0)]): ref
                           != r0#0)
                        {
                            assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2_0)];
                        }

                        if ($Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_0)]): ref
                             == r0#0
                           || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_0)]): ref
                             == r1#0)
                        {
                            assert defass#r#0;
                        }
                        else
                        {
                            assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2_0)];
                        }
                    }
                }

                // End Comprehension WF check
                assume true;
                assert $Is(Map#Glue((lambda $w#2_0: Box :: 
                      $Is($Unbox($w#2_0): ref, Tclass.M3.Element())
                         && Map#Domain(read($Heap, this, M3.UnionFind.M))[$w#2_0]), 
                    (lambda $w#2_0: Box :: 
                      $Box((if $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#2_0]): ref == r0#0
                             || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#2_0]): ref == r1#0
                           then r#0
                           else $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#2_0]): ref))), 
                    TMap(Tclass.M3.Element(), Tclass.M3.Element?())), 
                  TMap(Tclass.M3.Element(), Tclass.M3.Element()));
                $rhs#2_1 := Map#Glue((lambda $w#2_0: Box :: 
                    $Is($Unbox($w#2_0): ref, Tclass.M3.Element())
                       && Map#Domain(read($Heap, this, M3.UnionFind.M))[$w#2_0]), 
                  (lambda $w#2_0: Box :: 
                    $Box((if $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#2_0]): ref == r0#0
                           || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#2_0]): ref == r1#0
                         then r#0
                         else $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#2_0]): ref))), 
                  TMap(Tclass.M3.Element(), Tclass.M3.Element?()));
                $Heap := update($Heap, this, M3.UnionFind.M, $rhs#2_1);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(226,75)"} true;
                // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(227,9)
                if (*)
                {
                    // Assume Fuel Constant
                    havoc e#2_2;
                    assume $Is(e#2_2, Tclass.M3.Element());
                    assert {:subsumption 0} (forall f#2_0: ref :: 
                      { read($Heap, f#2_0, M3.Element.c) } 
                      $Is(f#2_0, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2_0)]
                           && M3.Contents.Link_q(read($Heap, f#2_0, M3.Element.c))
                         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#2_0, M3.Element.c)))]);
                    assume M3.UnionFind.Collect#canCall($Heap, this);
                    assume M3.UnionFind.Collect#canCall($Heap, this);
                    assume Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#2_2)];
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(230,32)
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    r0##2_0 := r1#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    r1##2_0 := r0#0;
                    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                    assert {:subsumption 0} (forall f#2_1: ref :: 
                      { read(old($Heap), f#2_1, M3.Element.c) } 
                      $Is(f#2_1, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#2_1)]
                           && M3.Contents.Link_q(read(old($Heap), f#2_1, M3.Element.c))
                         ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#2_1, M3.Element.c)))]);
                    assume (forall f#2_1: ref :: 
                      { read(old($Heap), f#2_1, M3.Element.c) } 
                      $Is(f#2_1, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#2_1)]
                           && M3.Contents.Link_q(read(old($Heap), f#2_1, M3.Element.c))
                         ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#2_1, M3.Element.c)))]);
                    assume M3.UnionFind.Collect#canCall(old($Heap), this);
                    assume M3.UnionFind.Collect#canCall(old($Heap), this);
                    // ProcessCallStmt: CheckSubrange
                    C##2_0 := M3.UnionFind.Collect(old($Heap), this);
                    assert {:subsumption 0} (forall f#2_2: ref :: 
                      { read($Heap, f#2_2, M3.Element.c) } 
                      $Is(f#2_2, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2_2)]
                           && M3.Contents.Link_q(read($Heap, f#2_2, M3.Element.c))
                         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#2_2, M3.Element.c)))]);
                    assume (forall f#2_2: ref :: 
                      { read($Heap, f#2_2, M3.Element.c) } 
                      $Is(f#2_2, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2_2)]
                           && M3.Contents.Link_q(read($Heap, f#2_2, M3.Element.c))
                         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#2_2, M3.Element.c)))]);
                    assume M3.UnionFind.Collect#canCall($Heap, this);
                    assume M3.UnionFind.Collect#canCall($Heap, this);
                    // ProcessCallStmt: CheckSubrange
                    C'##2_0 := M3.UnionFind.Collect($Heap, this);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call Call$$M3.UnionFind.JoinMaintainsReaches0(this, r0##2_0, r1##2_0, C##2_0, C'##2_0);
                    // TrCallStmt: After ProcessCallStmt
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(230,66)"} true;
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(231,11)
                    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                    assert {:subsumption 0} Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)];
                    assert {:subsumption 0} $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref
                       != null;
                    assert $IsAlloc($Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                      Tclass.M3.Element(), 
                      old($Heap));
                    assert M3.Contents.Root_q(read(old($Heap), 
                        $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                        M3.Element.c));
                    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                    assert {:subsumption 0} Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)];
                    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                    assert {:subsumption 0} (forall f#2_3: ref :: 
                      { read(old($Heap), f#2_3, M3.Element.c) } 
                      $Is(f#2_3, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#2_3)]
                           && M3.Contents.Link_q(read(old($Heap), f#2_3, M3.Element.c))
                         ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#2_3, M3.Element.c)))]);
                    assume M3.UnionFind.Collect#canCall(old($Heap), this);
                    ##d#2_0 := M3.Contents.depth(read(old($Heap), 
                        $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                        M3.Element.c));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##d#2_0, Tclass._System.nat(), $Heap);
                    ##e#2_0 := e#2_2;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##e#2_0, Tclass.M3.Element(), $Heap);
                    ##r#2_0 := $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##r#2_0, Tclass.M3.Element(), $Heap);
                    ##C#2_0 := M3.UnionFind.Collect(old($Heap), this);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##C#2_0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
                    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#2_0)
                       ==> M3.__default.GoodCMap(##C#2_0)
                         || (forall f#2_4: ref :: 
                          { $Unbox(Map#Elements(##C#2_0)[$Box(f#2_4)]): DatatypeType } 
                          $Is(f#2_4, Tclass.M3.Element?())
                             ==> 
                            Map#Domain(##C#2_0)[$Box(f#2_4)]
                               && M3.Contents.Link_q($Unbox(Map#Elements(##C#2_0)[$Box(f#2_4)]): DatatypeType)
                             ==> Map#Domain(##C#2_0)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#2_0)[$Box(f#2_4)]): DatatypeType))]);
                    assert {:subsumption 0} Map#Domain(##C#2_0)[$Box(##e#2_0)];
                    assume M3.UnionFind.Reaches#canCall(this, 
                      M3.Contents.depth(read(old($Heap), 
                          $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                          M3.Element.c)), 
                      e#2_2, 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                      M3.UnionFind.Collect(old($Heap), this));
                    assume M3.UnionFind.Collect#canCall(old($Heap), this)
                       && M3.UnionFind.Reaches#canCall(this, 
                        M3.Contents.depth(read(old($Heap), 
                            $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                            M3.Element.c)), 
                        e#2_2, 
                        $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                        M3.UnionFind.Collect(old($Heap), this));
                    assert {:subsumption 0} M3.UnionFind.Reaches($LS($LS($LZ)), 
                      this, 
                      M3.Contents.depth(read(old($Heap), 
                          $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                          M3.Element.c)), 
                      e#2_2, 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                      M3.UnionFind.Collect(old($Heap), this));
                    assume M3.UnionFind.Reaches($LS($LZ), 
                      this, 
                      M3.Contents.depth(read(old($Heap), 
                          $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                          M3.Element.c)), 
                      e#2_2, 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                      M3.UnionFind.Collect(old($Heap), this));
                    assert M3.Contents.Root_q(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                        M3.Element.c));
                    assert M3.UnionFind.Reaches($LS($LS($LZ)), 
                      this, 
                      M3.Contents.depth(read($Heap, 
                          $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                          M3.Element.c)), 
                      e#2_2, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_2)]): ref, 
                      M3.UnionFind.Collect($Heap, this));
                    assume false;
                }
                else
                {
                    assume (forall e#2_3: ref :: 
                      { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_3)]): ref } 
                        { Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#2_3)] } 
                      $Is(e#2_3, Tclass.M3.Element())
                           && Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#2_3)]
                         ==> M3.Contents.Root_q(read($Heap, 
                              $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_3)]): ref, 
                              M3.Element.c))
                           && M3.UnionFind.Reaches($LS($LZ), 
                            this, 
                            M3.Contents.depth(read($Heap, 
                                $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_3)]): ref, 
                                M3.Element.c)), 
                            e#2_3, 
                            $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2_3)]): ref, 
                            M3.UnionFind.Collect($Heap, this)));
                }

                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(232,8)"} true;
            }
            else
            {
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(234,14)
                assert r0#0 != null;
                assume true;
                assert $_Frame[r0#0, M3.Element.c];
                assume true;
                $rhs#0 := #M3.Contents.Link(r1#0);
                $Heap := update($Heap, r0#0, M3.Element.c, $rhs#0);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(234,24)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(235,14)
                assert r1#0 != null;
                assume true;
                assert $_Frame[r1#0, M3.Element.c];
                assert r1#0 != null;
                assert M3.Contents.Root_q(read($Heap, r1#0, M3.Element.c));
                assert $Is(M3.Contents.depth(read($Heap, r1#0, M3.Element.c)) + 1, Tclass._System.nat());
                assume true;
                $rhs#1 := #M3.Contents.Root(M3.Contents.depth(read($Heap, r1#0, M3.Element.c)) + 1);
                $Heap := update($Heap, r1#0, M3.Element.c, $rhs#1);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(235,36)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(236,11)
                assume true;
                assume true;
                r#0 := r1#0;
                defass#r#0 := true;
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(236,15)"} true;
                // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(237,11)
                assume true;
                assert $_Frame[this, M3.UnionFind.M];
                // Begin Comprehension WF check
                havoc e#18;
                if ($Is(e#18, Tclass.M3.Element()))
                {
                    if (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#18)])
                    {
                        assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#18)];
                        if ($Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]): ref != r0#0)
                        {
                            assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#18)];
                        }

                        if ($Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]): ref == r0#0
                           || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]): ref == r1#0)
                        {
                            assert defass#r#0;
                        }
                        else
                        {
                            assert Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#18)];
                        }
                    }
                }

                // End Comprehension WF check
                assume true;
                assert $Is(Map#Glue((lambda $w#3: Box :: 
                      $Is($Unbox($w#3): ref, Tclass.M3.Element())
                         && Map#Domain(read($Heap, this, M3.UnionFind.M))[$w#3]), 
                    (lambda $w#3: Box :: 
                      $Box((if $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#3]): ref == r0#0
                             || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#3]): ref == r1#0
                           then r#0
                           else $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#3]): ref))), 
                    TMap(Tclass.M3.Element(), Tclass.M3.Element?())), 
                  TMap(Tclass.M3.Element(), Tclass.M3.Element()));
                $rhs#2 := Map#Glue((lambda $w#3: Box :: 
                    $Is($Unbox($w#3): ref, Tclass.M3.Element())
                       && Map#Domain(read($Heap, this, M3.UnionFind.M))[$w#3]), 
                  (lambda $w#3: Box :: 
                    $Box((if $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#3]): ref == r0#0
                           || $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#3]): ref == r1#0
                         then r#0
                         else $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$w#3]): ref))), 
                  TMap(Tclass.M3.Element(), Tclass.M3.Element?()));
                $Heap := update($Heap, this, M3.UnionFind.M, $rhs#2);
                assume $IsGoodHeap($Heap);
                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(237,75)"} true;
                // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(238,9)
                if (*)
                {
                    // Assume Fuel Constant
                    havoc e#20;
                    assume $Is(e#20, Tclass.M3.Element());
                    assert {:subsumption 0} (forall f#0: ref :: 
                      { read($Heap, f#0, M3.Element.c) } 
                      $Is(f#0, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#0)]
                           && M3.Contents.Link_q(read($Heap, f#0, M3.Element.c))
                         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#0, M3.Element.c)))]);
                    assume M3.UnionFind.Collect#canCall($Heap, this);
                    assume M3.UnionFind.Collect#canCall($Heap, this);
                    assume Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#20)];
                    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(241,32)
                    // TrCallStmt: Before ProcessCallStmt
                    assume true;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    r0##0 := r0#0;
                    assume true;
                    // ProcessCallStmt: CheckSubrange
                    r1##0 := r1#0;
                    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                    assert {:subsumption 0} (forall f#1: ref :: 
                      { read(old($Heap), f#1, M3.Element.c) } 
                      $Is(f#1, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#1)]
                           && M3.Contents.Link_q(read(old($Heap), f#1, M3.Element.c))
                         ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#1, M3.Element.c)))]);
                    assume (forall f#1: ref :: 
                      { read(old($Heap), f#1, M3.Element.c) } 
                      $Is(f#1, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#1)]
                           && M3.Contents.Link_q(read(old($Heap), f#1, M3.Element.c))
                         ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#1, M3.Element.c)))]);
                    assume M3.UnionFind.Collect#canCall(old($Heap), this);
                    assume M3.UnionFind.Collect#canCall(old($Heap), this);
                    // ProcessCallStmt: CheckSubrange
                    C##0 := M3.UnionFind.Collect(old($Heap), this);
                    assert {:subsumption 0} (forall f#2: ref :: 
                      { read($Heap, f#2, M3.Element.c) } 
                      $Is(f#2, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]
                           && M3.Contents.Link_q(read($Heap, f#2, M3.Element.c))
                         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#2, M3.Element.c)))]);
                    assume (forall f#2: ref :: 
                      { read($Heap, f#2, M3.Element.c) } 
                      $Is(f#2, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]
                           && M3.Contents.Link_q(read($Heap, f#2, M3.Element.c))
                         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#2, M3.Element.c)))]);
                    assume M3.UnionFind.Collect#canCall($Heap, this);
                    assume M3.UnionFind.Collect#canCall($Heap, this);
                    // ProcessCallStmt: CheckSubrange
                    C'##0 := M3.UnionFind.Collect($Heap, this);
                    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                    // ProcessCallStmt: Make the call
                    call Call$$M3.UnionFind.JoinMaintainsReaches1(this, r0##0, r1##0, C##0, C'##0);
                    // TrCallStmt: After ProcessCallStmt
                    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(241,66)"} true;
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(242,11)
                    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                    assert {:subsumption 0} Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)];
                    assert {:subsumption 0} $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref
                       != null;
                    assert $IsAlloc($Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                      Tclass.M3.Element(), 
                      old($Heap));
                    assert M3.Contents.Root_q(read(old($Heap), 
                        $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                        M3.Element.c));
                    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                    assert {:subsumption 0} Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)];
                    assert $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
                    assert {:subsumption 0} (forall f#3: ref :: 
                      { read(old($Heap), f#3, M3.Element.c) } 
                      $Is(f#3, Tclass.M3.Element())
                         ==> 
                        Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#3)]
                           && M3.Contents.Link_q(read(old($Heap), f#3, M3.Element.c))
                         ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#3, M3.Element.c)))]);
                    assume M3.UnionFind.Collect#canCall(old($Heap), this);
                    ##d#0 := M3.Contents.depth(read(old($Heap), 
                        $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                        M3.Element.c));
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
                    ##e#0 := e#20;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
                    ##r#0 := $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
                    ##C#0 := M3.UnionFind.Collect(old($Heap), this);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
                    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#0)
                       ==> M3.__default.GoodCMap(##C#0)
                         || (forall f#4: ref :: 
                          { $Unbox(Map#Elements(##C#0)[$Box(f#4)]): DatatypeType } 
                          $Is(f#4, Tclass.M3.Element?())
                             ==> 
                            Map#Domain(##C#0)[$Box(f#4)]
                               && M3.Contents.Link_q($Unbox(Map#Elements(##C#0)[$Box(f#4)]): DatatypeType)
                             ==> Map#Domain(##C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#0)[$Box(f#4)]): DatatypeType))]);
                    assert {:subsumption 0} Map#Domain(##C#0)[$Box(##e#0)];
                    assume M3.UnionFind.Reaches#canCall(this, 
                      M3.Contents.depth(read(old($Heap), 
                          $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                          M3.Element.c)), 
                      e#20, 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                      M3.UnionFind.Collect(old($Heap), this));
                    assume M3.UnionFind.Collect#canCall(old($Heap), this)
                       && M3.UnionFind.Reaches#canCall(this, 
                        M3.Contents.depth(read(old($Heap), 
                            $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                            M3.Element.c)), 
                        e#20, 
                        $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                        M3.UnionFind.Collect(old($Heap), this));
                    assert {:subsumption 0} M3.UnionFind.Reaches($LS($LS($LZ)), 
                      this, 
                      M3.Contents.depth(read(old($Heap), 
                          $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                          M3.Element.c)), 
                      e#20, 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                      M3.UnionFind.Collect(old($Heap), this));
                    assume M3.UnionFind.Reaches($LS($LZ), 
                      this, 
                      M3.Contents.depth(read(old($Heap), 
                          $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                          M3.Element.c)), 
                      e#20, 
                      $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                      M3.UnionFind.Collect(old($Heap), this));
                    assert M3.Contents.Root_q(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                        M3.Element.c));
                    assert M3.UnionFind.Reaches($LS($LS($LZ)), 
                      this, 
                      M3.Contents.depth(read($Heap, 
                          $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                          M3.Element.c)), 
                      e#20, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#20)]): ref, 
                      M3.UnionFind.Collect($Heap, this));
                    assume false;
                }
                else
                {
                    assume (forall e#21: ref :: 
                      { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#21)]): ref } 
                        { Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#21)] } 
                      $Is(e#21, Tclass.M3.Element())
                           && Map#Domain(M3.UnionFind.Collect($Heap, this))[$Box(e#21)]
                         ==> M3.Contents.Root_q(read($Heap, 
                              $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#21)]): ref, 
                              M3.Element.c))
                           && M3.UnionFind.Reaches($LS($LZ), 
                            this, 
                            M3.Contents.depth(read($Heap, 
                                $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#21)]): ref, 
                                M3.Element.c)), 
                            e#21, 
                            $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#21)]): ref, 
                            M3.UnionFind.Collect($Heap, this)));
                }

                assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(243,8)"} true;
            }
        }
    }

    assert defass#r#0;
}



procedure {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} CheckWellformed$$M3.UnionFind.JoinMaintainsReaches1(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} CheckWellformed$$M3.UnionFind.JoinMaintainsReaches1(this: ref, r0#0: ref, r1#0: ref, C#0: Map Box Box, C'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##C#0: Map Box Box;
  var ##C#1: Map Box Box;
  var d#0: int;
  var e#0: ref;
  var r#0: ref;
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#2: Map Box Box;
  var ##d#1: int;
  var ##e#1: ref;
  var ##r#1: ref;
  var ##C#3: Map Box Box;
  var e#2: ref;
  var ##d#2: int;
  var ##e#2: ref;
  var ##r#2: ref;
  var ##C#4: Map Box Box;
  var ##d#3: int;
  var ##e#3: ref;
  var ##r#3: ref;
  var ##C#5: Map Box Box;
  var e#4: ref;
  var ##d#4: int;
  var ##e#4: ref;
  var ##r#4: ref;
  var ##C#6: Map Box Box;
  var ##d#5: int;
  var ##e#5: ref;
  var ##r#5: ref;
  var ##C#7: Map Box Box;

    // AddMethodImpl: JoinMaintainsReaches1, CheckWellformed$$M3.UnionFind.JoinMaintainsReaches1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(247,33): initial state"} true;
    ##C#0 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C#0);
    assume M3.__default.GoodCMap(C#0);
    assume Map#Domain(C#0)[$Box(r0#0)];
    assume Map#Domain(C#0)[$Box(r1#0)];
    assert Map#Domain(C#0)[$Box(r0#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r0#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
       == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume r0#0 != r1#0;
    assert Map#Domain(C#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert $Is(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1, 
      Tclass._System.nat());
    assume Map#Equal(C'#0, 
      Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
        $Box(r1#0), 
        $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
    ##C#1 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#1, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C'#0);
    assume M3.__default.GoodCMap(C'#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(252,14): post-state"} true;
    havoc d#0;
    havoc e#0;
    havoc r#0;
    assume LitInt(0) <= d#0
       && $Is(e#0, Tclass.M3.Element())
       && $Is(r#0, Tclass.M3.Element());
    if (*)
    {
        assume Map#Domain(C#0)[$Box(e#0)];
        ##d#0 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
        ##e#0 := e#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
        ##r#0 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
        ##C#2 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#2, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#2)
           ==> M3.__default.GoodCMap(##C#2)
             || (forall f#0: ref :: 
              { $Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType } 
              $Is(f#0, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#2)[$Box(f#0)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType)
                 ==> Map#Domain(##C#2)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#2);
        assert {:subsumption 0} Map#Domain(##C#2)[$Box(##e#0)];
        assume Map#Domain(##C#2)[$Box(##e#0)];
        assume M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C#0);
        assume M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C#0);
        assume r#0 != r0#0;
        assume r#0 != r1#0;
        ##d#1 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, Tclass._System.nat(), $Heap);
        ##e#1 := e#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#1, Tclass.M3.Element(), $Heap);
        ##r#1 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#1, Tclass.M3.Element(), $Heap);
        ##C#3 := C'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#3, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#3)
           ==> M3.__default.GoodCMap(##C#3)
             || (forall f#1: ref :: 
              { $Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType } 
              $Is(f#1, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#3)[$Box(f#1)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType)
                 ==> Map#Domain(##C#3)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#3);
        assert {:subsumption 0} Map#Domain(##C#3)[$Box(##e#1)];
        assume Map#Domain(##C#3)[$Box(##e#1)];
        assume M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
        assume M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C'#0);
    }
    else
    {
        assume Map#Domain(C#0)[$Box(e#0)]
             && M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C#0)
             && r#0 != r0#0
             && r#0 != r1#0
           ==> M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C'#0);
    }

    assume (forall d#1: int, e#1: ref, r#1: ref :: 
      {:induction} {:_induction d#1, e#1, r#1} { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
        { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
      LitInt(0) <= d#1
           && $Is(e#1, Tclass.M3.Element())
           && $Is(r#1, Tclass.M3.Element())
         ==> 
        Map#Domain(C#0)[$Box(e#1)]
           && M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
           && r#1 != r0#0
           && r#1 != r1#0
         ==> M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0));
    havoc e#2;
    assume $Is(e#2, Tclass.M3.Element());
    if (*)
    {
        assume Map#Domain(C#0)[$Box(e#2)];
        assert Map#Domain(C#0)[$Box(r0#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        ##d#2 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#2, Tclass._System.nat(), $Heap);
        ##e#2 := e#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#2, Tclass.M3.Element(), $Heap);
        ##r#2 := r0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#2, Tclass.M3.Element(), $Heap);
        ##C#4 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#4, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#4)
           ==> M3.__default.GoodCMap(##C#4)
             || (forall f#2: ref :: 
              { $Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType } 
              $Is(f#2, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#4)[$Box(f#2)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType)
                 ==> Map#Domain(##C#4)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#4);
        assert {:subsumption 0} Map#Domain(##C#4)[$Box(##e#2)];
        assume Map#Domain(##C#4)[$Box(##e#2)];
        assume M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#2, 
          r0#0, 
          C#0);
        assume M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#2, 
          r0#0, 
          C#0);
        assert Map#Domain(C'#0)[$Box(r1#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
        ##d#3 := M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#3, Tclass._System.nat(), $Heap);
        ##e#3 := e#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#3, Tclass.M3.Element(), $Heap);
        ##r#3 := r1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#3, Tclass.M3.Element(), $Heap);
        ##C#5 := C'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#5, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#5)
           ==> M3.__default.GoodCMap(##C#5)
             || (forall f#3: ref :: 
              { $Unbox(Map#Elements(##C#5)[$Box(f#3)]): DatatypeType } 
              $Is(f#3, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#5)[$Box(f#3)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#5)[$Box(f#3)]): DatatypeType)
                 ==> Map#Domain(##C#5)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#5)[$Box(f#3)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#5);
        assert {:subsumption 0} Map#Domain(##C#5)[$Box(##e#3)];
        assume Map#Domain(##C#5)[$Box(##e#3)];
        assume M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#2, 
          r1#0, 
          C'#0);
        assume M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#2, 
          r1#0, 
          C'#0);
    }
    else
    {
        assume Map#Domain(C#0)[$Box(e#2)]
             && M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
              e#2, 
              r0#0, 
              C#0)
           ==> M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
            e#2, 
            r1#0, 
            C'#0);
    }

    assume (forall e#3: ref :: 
      { M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#3, 
          r1#0, 
          C'#0) } 
        { M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0) } 
        { Map#Domain(C#0)[$Box(e#3)] } 
      $Is(e#3, Tclass.M3.Element())
         ==> 
        Map#Domain(C#0)[$Box(e#3)]
           && M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#3, 
            r0#0, 
            C#0)
         ==> M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#3, 
          r1#0, 
          C'#0));
    havoc e#4;
    assume $Is(e#4, Tclass.M3.Element());
    if (*)
    {
        assume Map#Domain(C#0)[$Box(e#4)];
        assert Map#Domain(C#0)[$Box(r1#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
        ##d#4 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#4, Tclass._System.nat(), $Heap);
        ##e#4 := e#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#4, Tclass.M3.Element(), $Heap);
        ##r#4 := r1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#4, Tclass.M3.Element(), $Heap);
        ##C#6 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#6, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#6)
           ==> M3.__default.GoodCMap(##C#6)
             || (forall f#4: ref :: 
              { $Unbox(Map#Elements(##C#6)[$Box(f#4)]): DatatypeType } 
              $Is(f#4, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#6)[$Box(f#4)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#6)[$Box(f#4)]): DatatypeType)
                 ==> Map#Domain(##C#6)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#6)[$Box(f#4)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#6);
        assert {:subsumption 0} Map#Domain(##C#6)[$Box(##e#4)];
        assume Map#Domain(##C#6)[$Box(##e#4)];
        assume M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#4, 
          r1#0, 
          C#0);
        assume M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#4, 
          r1#0, 
          C#0);
        assert Map#Domain(C'#0)[$Box(r1#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
        ##d#5 := M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#5, Tclass._System.nat(), $Heap);
        ##e#5 := e#4;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#5, Tclass.M3.Element(), $Heap);
        ##r#5 := r1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#5, Tclass.M3.Element(), $Heap);
        ##C#7 := C'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#7, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#7)
           ==> M3.__default.GoodCMap(##C#7)
             || (forall f#5: ref :: 
              { $Unbox(Map#Elements(##C#7)[$Box(f#5)]): DatatypeType } 
              $Is(f#5, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#7)[$Box(f#5)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#7)[$Box(f#5)]): DatatypeType)
                 ==> Map#Domain(##C#7)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#7)[$Box(f#5)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#7);
        assert {:subsumption 0} Map#Domain(##C#7)[$Box(##e#5)];
        assume Map#Domain(##C#7)[$Box(##e#5)];
        assume M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#4, 
          r1#0, 
          C'#0);
        assume M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#4, 
          r1#0, 
          C'#0);
    }
    else
    {
        assume Map#Domain(C#0)[$Box(e#4)]
             && M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
              e#4, 
              r1#0, 
              C#0)
           ==> M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
            e#4, 
            r1#0, 
            C'#0);
    }

    assume (forall e#5: ref :: 
      { M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#5, 
          r1#0, 
          C'#0) } 
        { M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#5, 
          r1#0, 
          C#0) } 
        { Map#Domain(C#0)[$Box(e#5)] } 
      $Is(e#5, Tclass.M3.Element())
         ==> 
        Map#Domain(C#0)[$Box(e#5)]
           && M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
            e#5, 
            r1#0, 
            C#0)
         ==> M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#5, 
          r1#0, 
          C'#0));
}



procedure {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} Call$$M3.UnionFind.JoinMaintainsReaches1(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#6: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType } 
        $Is(f#6, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#6)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
     == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires r0#0 != r1#0;
  requires Map#Equal(C'#0, 
    Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
      $Box(r1#0), 
      $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
  requires M3.__default.GoodCMap#canCall(C'#0)
     ==> M3.__default.GoodCMap(C'#0)
       || (forall f#7: ref :: 
        { $Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType } 
        $Is(f#7, Tclass.M3.Element?())
           ==> 
          Map#Domain(C'#0)[$Box(f#7)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType)
           ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
       ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C#0)
         && (M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
           ==> 
          r#1 != r0#0
           ==> 
          r#1 != r1#0
           ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C'#0)));
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    {:induction} {:_induction d#1, e#1, r#1} { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
         && M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
         && r#1 != r0#0
         && r#1 != r1#0
       ==> M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0));
  free ensures (forall e#3: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
        e#3, 
        r0#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#3)] } 
    $Is(e#3, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#3)]
       ==> M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0)
         && (M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#3, 
            r0#0, 
            C#0)
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
            e#3, 
            r1#0, 
            C'#0)));
  free ensures (forall e#3: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
        e#3, 
        r0#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#3)] } 
    $Is(e#3, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#3)]
         && M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0)
       ==> M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0));
  free ensures (forall e#5: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#5)] } 
    $Is(e#5, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#5)]
       ==> M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#5, 
          r1#0, 
          C#0)
         && (M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
            e#5, 
            r1#0, 
            C#0)
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
            e#5, 
            r1#0, 
            C'#0)));
  free ensures (forall e#5: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#5)] } 
    $Is(e#5, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#5)]
         && M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#5, 
          r1#0, 
          C#0)
       ==> M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C'#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} Impl$$M3.UnionFind.JoinMaintainsReaches1(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#8: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#8)]): DatatypeType } 
      $Is(f#8, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#8)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#8)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#8)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
     == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires r0#0 != r1#0;
  requires Map#Equal(C'#0, 
    Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
      $Box(r1#0), 
      $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
  free requires M3.__default.GoodCMap#canCall(C'#0)
     && 
    M3.__default.GoodCMap(C'#0)
     && (forall f#9: ref :: 
      { $Unbox(Map#Elements(C'#0)[$Box(f#9)]): DatatypeType } 
      $Is(f#9, Tclass.M3.Element?())
         ==> 
        Map#Domain(C'#0)[$Box(f#9)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#9)]): DatatypeType)
         ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#9)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
       ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C#0)
         && (M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
           ==> 
          r#1 != r0#0
           ==> 
          r#1 != r1#0
           ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C'#0)));
  ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
         && (forall d$ih#1#0: int, e$ih#1#0: ref, r$ih#1#0: ref :: 
          { M3.UnionFind.Reaches($LS($LZ), this, d$ih#1#0, e$ih#1#0, r$ih#1#0, C'#0) } 
            { M3.UnionFind.Reaches($LS($LZ), this, d$ih#1#0, e$ih#1#0, r$ih#1#0, C#0) } 
          LitInt(0) <= d$ih#1#0
               && $Is(e$ih#1#0, Tclass.M3.Element())
               && $Is(r$ih#1#0, Tclass.M3.Element())
             ==> 
            (0 <= d$ih#1#0 && d$ih#1#0 < d#1)
               || (d$ih#1#0 == d#1
                 && ((e$ih#1#0 == null && e#1 != null)
                   || ((e$ih#1#0 != null <==> e#1 != null) && r$ih#1#0 == null && r#1 != null)))
             ==> 
            Map#Domain(C#0)[$Box(e$ih#1#0)]
               && M3.UnionFind.Reaches($LS($LZ), this, d$ih#1#0, e$ih#1#0, r$ih#1#0, C#0)
               && r$ih#1#0 != r0#0
               && r$ih#1#0 != r1#0
             ==> M3.UnionFind.Reaches($LS($LZ), this, d$ih#1#0, e$ih#1#0, r$ih#1#0, C'#0))
         && true
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
         && M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C#0)
         && r#1 != r0#0
         && r#1 != r1#0
       ==> M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C'#0));
  free ensures (forall e#3: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
        e#3, 
        r0#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#3)] } 
    $Is(e#3, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#3)]
       ==> M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0)
         && (M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#3, 
            r0#0, 
            C#0)
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
            e#3, 
            r1#0, 
            C'#0)));
  ensures (forall e#3: ref :: 
    { M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
        e#3, 
        r0#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#3)] } 
    $Is(e#3, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#3)]
         && M3.UnionFind.Reaches($LS($LS($LZ)), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0)
       ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0));
  free ensures (forall e#5: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#5)] } 
    $Is(e#5, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#5)]
       ==> M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#5, 
          r1#0, 
          C#0)
         && (M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
            e#5, 
            r1#0, 
            C#0)
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
            e#5, 
            r1#0, 
            C'#0)));
  ensures (forall e#5: ref :: 
    { M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#5)] } 
    $Is(e#5, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#5)]
         && M3.UnionFind.Reaches($LS($LS($LZ)), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#5, 
          r1#0, 
          C#0)
       ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
        e#5, 
        r1#0, 
        C'#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} Impl$$M3.UnionFind.JoinMaintainsReaches1(this: ref, r0#0: ref, r1#0: ref, C#0: Map Box Box, C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var e#9: ref;
  var ##d#6: int;
  var ##e#6: ref;
  var ##r#6: ref;
  var ##C#8: Map Box Box;
  var e##0: ref;
  var C##0: Map Box Box;
  var d0##0: int;
  var d1##0: int;
  var r0##0: ref;
  var r1##0: ref;
  var C'##0: Map Box Box;
  var e#11: ref;
  var ##d#7: int;
  var ##e#7: ref;
  var ##r#7: ref;
  var ##C#9: Map Box Box;
  var d##0: int;
  var e##1: ref;
  var r##0: ref;
  var C##1: Map Box Box;
  var td##0: int;
  var r0##1: ref;
  var r1##1: ref;
  var C'##1: Map Box Box;

    // AddMethodImpl: JoinMaintainsReaches1, Impl$$M3.UnionFind.JoinMaintainsReaches1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(255,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#r00#0: ref, 
        $ih#r10#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && $Is($ih#r00#0, Tclass.M3.Element())
           && $Is($ih#r10#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#r00#0)]
           && Map#Domain($ih#C0#0)[$Box($ih#r10#0)]
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
             == M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && $ih#r00#0 != $ih#r10#0
           && Map#Equal($ih#C'0#0, 
            Map#Build(Map#Build($ih#C0#0, $Box($ih#r00#0), $Box(#M3.Contents.Link($ih#r10#0))), 
              $Box($ih#r10#0), 
              $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
                     + 1))))
           && M3.__default.GoodCMap($ih#C'0#0)
           && (($ih#r00#0 == null && r0#0 != null)
             || (($ih#r00#0 != null <==> r0#0 != null)
               && (($ih#r10#0 == null && r1#0 != null)
                 || (($ih#r10#0 != null <==> r1#0 != null)
                   && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                       && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                     || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                       && 
                      Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                       && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))
         ==> (forall d#2: int, e#6: ref, r#2: ref :: 
            {:induction} {:_induction d#2, e#6, r#2} { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#6, r#2, $ih#C'0#0) } 
              { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#6, r#2, $ih#C0#0) } 
            LitInt(0) <= d#2
                 && $Is(e#6, Tclass.M3.Element())
                 && $Is(r#2, Tclass.M3.Element())
               ==> 
              Map#Domain($ih#C0#0)[$Box(e#6)]
                 && M3.UnionFind.Reaches($LS($LZ), this, d#2, e#6, r#2, $ih#C0#0)
                 && r#2 != $ih#r00#0
                 && r#2 != $ih#r10#0
               ==> M3.UnionFind.Reaches($LS($LZ), this, d#2, e#6, r#2, $ih#C'0#0))
           && (forall e#7: ref :: 
            { M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#r10#0)]): DatatypeType), 
                e#7, 
                $ih#r10#0, 
                $ih#C'0#0) } 
              { M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType), 
                e#7, 
                $ih#r00#0, 
                $ih#C0#0) } 
              { Map#Domain($ih#C0#0)[$Box(e#7)] } 
            $Is(e#7, Tclass.M3.Element())
               ==> 
              Map#Domain($ih#C0#0)[$Box(e#7)]
                 && M3.UnionFind.Reaches($LS($LZ), 
                  this, 
                  M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType), 
                  e#7, 
                  $ih#r00#0, 
                  $ih#C0#0)
               ==> M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#r10#0)]): DatatypeType), 
                e#7, 
                $ih#r10#0, 
                $ih#C'0#0))
           && (forall e#8: ref :: 
            { M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#r10#0)]): DatatypeType), 
                e#8, 
                $ih#r10#0, 
                $ih#C'0#0) } 
              { M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType), 
                e#8, 
                $ih#r10#0, 
                $ih#C0#0) } 
              { Map#Domain($ih#C0#0)[$Box(e#8)] } 
            $Is(e#8, Tclass.M3.Element())
               ==> 
              Map#Domain($ih#C0#0)[$Box(e#8)]
                 && M3.UnionFind.Reaches($LS($LZ), 
                  this, 
                  M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType), 
                  e#8, 
                  $ih#r10#0, 
                  $ih#C0#0)
               ==> M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#r10#0)]): DatatypeType), 
                e#8, 
                $ih#r10#0, 
                $ih#C'0#0)));
    $_reverifyPost := false;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(256,7)
    if (*)
    {
        // Assume Fuel Constant
        havoc e#9;
        assume $Is(e#9, Tclass.M3.Element());
        if (Map#Domain(C#0)[$Box(e#9)])
        {
            assert {:subsumption 0} Map#Domain(C#0)[$Box(r0#0)];
            assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
            ##d#6 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#6, Tclass._System.nat(), $Heap);
            ##e#6 := e#9;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#6, Tclass.M3.Element(), $Heap);
            ##r#6 := r0#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#6, Tclass.M3.Element(), $Heap);
            ##C#8 := C#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#8, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
            assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#8)
               ==> M3.__default.GoodCMap(##C#8)
                 || (forall f#10: ref :: 
                  { $Unbox(Map#Elements(##C#8)[$Box(f#10)]): DatatypeType } 
                  $Is(f#10, Tclass.M3.Element?())
                     ==> 
                    Map#Domain(##C#8)[$Box(f#10)]
                       && M3.Contents.Link_q($Unbox(Map#Elements(##C#8)[$Box(f#10)]): DatatypeType)
                     ==> Map#Domain(##C#8)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#8)[$Box(f#10)]): DatatypeType))]);
            assert {:subsumption 0} Map#Domain(##C#8)[$Box(##e#6)];
            assume M3.UnionFind.Reaches#canCall(this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
              e#9, 
              r0#0, 
              C#0);
        }

        assume Map#Domain(C#0)[$Box(e#9)]
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#9, 
            r0#0, 
            C#0);
        assume Map#Domain(C#0)[$Box(e#9)]
           && M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#9, 
            r0#0, 
            C#0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(259,23)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##0 := e#9;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##0 := C#0;
        assert Map#Domain(C#0)[$Box(r0#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        d0##0 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        assert Map#Domain(C'#0)[$Box(r1#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        d1##0 := M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        r0##0 := r0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r1##0 := r1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C'##0 := C'#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.ExtendedReach_k(this, e##0, C##0, d0##0, d1##0, r0##0, r1##0, C'##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(259,67)"} true;
        assert M3.UnionFind.Reaches($LS($LS($LZ)), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#9, 
          r1#0, 
          C'#0);
        assume false;
    }
    else
    {
        assume (forall e#10: ref :: 
          { M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
              e#10, 
              r1#0, 
              C'#0) } 
            { M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
              e#10, 
              r0#0, 
              C#0) } 
            { Map#Domain(C#0)[$Box(e#10)] } 
          $Is(e#10, Tclass.M3.Element())
               && 
              Map#Domain(C#0)[$Box(e#10)]
               && M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
                e#10, 
                r0#0, 
                C#0)
             ==> M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
              e#10, 
              r1#0, 
              C'#0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(260,6)"} true;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(261,7)
    if (*)
    {
        // Assume Fuel Constant
        havoc e#11;
        assume $Is(e#11, Tclass.M3.Element());
        if (Map#Domain(C#0)[$Box(e#11)])
        {
            assert {:subsumption 0} Map#Domain(C#0)[$Box(r1#0)];
            assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
            ##d#7 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#7, Tclass._System.nat(), $Heap);
            ##e#7 := e#11;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#7, Tclass.M3.Element(), $Heap);
            ##r#7 := r1#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#7, Tclass.M3.Element(), $Heap);
            ##C#9 := C#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#9, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
            assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#9)
               ==> M3.__default.GoodCMap(##C#9)
                 || (forall f#11: ref :: 
                  { $Unbox(Map#Elements(##C#9)[$Box(f#11)]): DatatypeType } 
                  $Is(f#11, Tclass.M3.Element?())
                     ==> 
                    Map#Domain(##C#9)[$Box(f#11)]
                       && M3.Contents.Link_q($Unbox(Map#Elements(##C#9)[$Box(f#11)]): DatatypeType)
                     ==> Map#Domain(##C#9)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#9)[$Box(f#11)]): DatatypeType))]);
            assert {:subsumption 0} Map#Domain(##C#9)[$Box(##e#7)];
            assume M3.UnionFind.Reaches#canCall(this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
              e#11, 
              r1#0, 
              C#0);
        }

        assume Map#Domain(C#0)[$Box(e#11)]
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
            e#11, 
            r1#0, 
            C#0);
        assume Map#Domain(C#0)[$Box(e#11)]
           && M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
            e#11, 
            r1#0, 
            C#0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(264,41)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assert Map#Domain(C#0)[$Box(r1#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##1 := e#11;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r##0 := r1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##1 := C#0;
        assert Map#Domain(C#0)[$Box(r0#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        td##0 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        r0##1 := r0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r1##1 := r1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C'##1 := C'#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.ReachUnaffectedByChangeFromRoot_k(this, d##0, e##1, r##0, C##1, td##0, r0##1, r1##1, C'##1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(264,88)"} true;
        assert M3.UnionFind.Reaches($LS($LS($LZ)), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
          e#11, 
          r1#0, 
          C'#0);
        assume false;
    }
    else
    {
        assume (forall e#12: ref :: 
          { M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
              e#12, 
              r1#0, 
              C'#0) } 
            { M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
              e#12, 
              r1#0, 
              C#0) } 
            { Map#Domain(C#0)[$Box(e#12)] } 
          $Is(e#12, Tclass.M3.Element())
               && 
              Map#Domain(C#0)[$Box(e#12)]
               && M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
                e#12, 
                r1#0, 
                C#0)
             ==> M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType), 
              e#12, 
              r1#0, 
              C'#0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(265,6)"} true;
}



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, r0#0, C'#0} CheckWellformed$$M3.UnionFind.ReachUnaffectedByChangeFromRoot_k(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, r0#0, C'#0} CheckWellformed$$M3.UnionFind.ReachUnaffectedByChangeFromRoot_k(this: ref, 
    d#0: int, 
    e#0: ref, 
    r#0: ref, 
    C#0: Map Box Box, 
    td#0: int, 
    r0#0: ref, 
    r1#0: ref, 
    C'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##C#0: Map Box Box;
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#1: Map Box Box;
  var ##d#1: int;
  var ##e#1: ref;
  var ##r#1: ref;
  var ##C#2: Map Box Box;
  var ##C#3: Map Box Box;
  var ##d#2: int;
  var ##e#2: ref;
  var ##r#2: ref;
  var ##C#4: Map Box Box;

    // AddMethodImpl: ReachUnaffectedByChangeFromRoot', CheckWellformed$$M3.UnionFind.ReachUnaffectedByChangeFromRoot_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(268,33): initial state"} true;
    ##C#0 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C#0);
    assume M3.__default.GoodCMap(C#0);
    assume Map#Domain(C#0)[$Box(e#0)];
    ##d#0 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
    ##e#0 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
    ##r#0 := r#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
    ##C#1 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#1, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#1)
       ==> M3.__default.GoodCMap(##C#1)
         || (forall f#0: ref :: 
          { $Unbox(Map#Elements(##C#1)[$Box(f#0)]): DatatypeType } 
          $Is(f#0, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#1)[$Box(f#0)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#1)[$Box(f#0)]): DatatypeType)
             ==> Map#Domain(##C#1)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#1)[$Box(f#0)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#1);
    assert {:subsumption 0} Map#Domain(##C#1)[$Box(##e#0)];
    assume Map#Domain(##C#1)[$Box(##e#0)];
    assume M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C#0);
    assume Map#Domain(C#0)[$Box(r0#0)];
    assume Map#Domain(C#0)[$Box(r1#0)];
    assert Map#Domain(C#0)[$Box(r0#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r0#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
       == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume r0#0 != r1#0;
    assert Map#Domain(C#0)[$Box(r0#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert $Is(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1, 
      Tclass._System.nat());
    assume Map#Equal(C'#0, 
      Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
        $Box(r1#0), 
        $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
    ##d#1 := td#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, Tclass._System.nat(), $Heap);
    ##e#1 := r0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#1, Tclass.M3.Element(), $Heap);
    ##r#1 := r0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#1, Tclass.M3.Element(), $Heap);
    ##C#2 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#2, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#2)
       ==> M3.__default.GoodCMap(##C#2)
         || (forall f#1: ref :: 
          { $Unbox(Map#Elements(##C#2)[$Box(f#1)]): DatatypeType } 
          $Is(f#1, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#2)[$Box(f#1)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#2)[$Box(f#1)]): DatatypeType)
             ==> Map#Domain(##C#2)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#2)[$Box(f#1)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#2);
    assert {:subsumption 0} Map#Domain(##C#2)[$Box(##e#1)];
    assume Map#Domain(##C#2)[$Box(##e#1)];
    assume M3.UnionFind.Reaches#canCall(this, td#0, r0#0, r0#0, C#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, td#0, r0#0, r0#0, C#0);
    assume r0#0 != r#0;
    ##C#3 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#3, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C'#0);
    assume M3.__default.GoodCMap(C'#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(275,21): post-state"} true;
    assert $Is(d#0 + 1, Tclass._System.nat());
    ##d#2 := d#0 + 1;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#2, Tclass._System.nat(), $Heap);
    ##e#2 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#2, Tclass.M3.Element(), $Heap);
    ##r#2 := r#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#2, Tclass.M3.Element(), $Heap);
    ##C#4 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#4, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#4)
       ==> M3.__default.GoodCMap(##C#4)
         || (forall f#2: ref :: 
          { $Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType } 
          $Is(f#2, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#4)[$Box(f#2)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType)
             ==> Map#Domain(##C#4)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#4);
    assert {:subsumption 0} Map#Domain(##C#4)[$Box(##e#2)];
    assume Map#Domain(##C#4)[$Box(##e#2)];
    assume M3.UnionFind.Reaches#canCall(this, d#0 + 1, e#0, r#0, C'#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, d#0 + 1, e#0, r#0, C'#0);
}



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, r0#0, C'#0} Call$$M3.UnionFind.ReachUnaffectedByChangeFromRoot_k(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#3: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType } 
        $Is(f#3, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#3)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C#0);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
     == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires r0#0 != r1#0;
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires Map#Equal(C'#0, 
    Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
      $Box(r1#0), 
      $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, td#0, r0#0, r0#0, C#0);
  requires r0#0 != r#0;
  requires M3.__default.GoodCMap#canCall(C'#0)
     ==> M3.__default.GoodCMap(C'#0)
       || (forall f#4: ref :: 
        { $Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType } 
        $Is(f#4, Tclass.M3.Element?())
           ==> 
          Map#Domain(C'#0)[$Box(f#4)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType)
           ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d#0 + 1, e#0, r#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0 + 1, e#0, r#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, r0#0, C'#0} Impl$$M3.UnionFind.ReachUnaffectedByChangeFromRoot_k(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#5: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType } 
      $Is(f#5, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#5)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C#0);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
     == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires r0#0 != r1#0;
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires Map#Equal(C'#0, 
    Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
      $Box(r1#0), 
      $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, td#0, r0#0, r0#0, C#0);
  requires r0#0 != r#0;
  free requires M3.__default.GoodCMap#canCall(C'#0)
     && 
    M3.__default.GoodCMap(C'#0)
     && (forall f#6: ref :: 
      { $Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType } 
      $Is(f#6, Tclass.M3.Element?())
         ==> 
        Map#Domain(C'#0)[$Box(f#6)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType)
         ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d#0 + 1, e#0, r#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0 + 1, e#0, r#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, r0#0, C'#0} Impl$$M3.UnionFind.ReachUnaffectedByChangeFromRoot_k(this: ref, 
    d#0: int, 
    e#0: ref, 
    r#0: ref, 
    C#0: Map Box Box, 
    td#0: int, 
    r0#0: ref, 
    r1#0: ref, 
    C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: ReachUnaffectedByChangeFromRoot', Impl$$M3.UnionFind.ReachUnaffectedByChangeFromRoot_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(276,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#d0#0: int, 
        $ih#e0#0: ref, 
        $ih#r0#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#td0#0: int, 
        $ih#r00#0: ref, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && LitInt(0) <= $ih#d0#0
           && $Is($ih#e0#0, Tclass.M3.Element())
           && $Is($ih#r0#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && LitInt(0) <= $ih#td0#0
           && $Is($ih#r00#0, Tclass.M3.Element())
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#e0#0)]
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#d0#0, $ih#e0#0, $ih#r0#0, $ih#C0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#r00#0)]
           && Map#Domain($ih#C0#0)[$Box(r1#0)]
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box(r1#0)]): DatatypeType)
           && M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
             == M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box(r1#0)]): DatatypeType)
           && $ih#r00#0 != r1#0
           && 
          M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && Map#Equal($ih#C'0#0, 
            Map#Build(Map#Build($ih#C0#0, $Box($ih#r00#0), $Box(#M3.Contents.Link(r1#0))), 
              $Box(r1#0), 
              $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box(r1#0)]): DatatypeType) + 1))))
           && 
          M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#td0#0, $ih#r00#0, $ih#r00#0, $ih#C0#0)
           && $ih#r00#0 != $ih#r0#0
           && M3.__default.GoodCMap($ih#C'0#0)
           && ((0 <= $ih#d0#0 && $ih#d0#0 < d#0)
             || ($ih#d0#0 == d#0
               && (($ih#e0#0 == null && e#0 != null)
                 || (($ih#e0#0 != null <==> e#0 != null)
                   && (($ih#r0#0 == null && r#0 != null)
                     || (($ih#r0#0 != null <==> r#0 != null)
                       && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                         || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && ((0 <= $ih#td0#0 && $ih#td0#0 < td#0)
                             || ($ih#td0#0 == td#0
                               && (($ih#r00#0 == null && r0#0 != null)
                                 || (($ih#r00#0 != null <==> r0#0 != null)
                                   && ((r1#0 == null && r1#0 != null)
                                     || ((r1#0 != null <==> r1#0 != null)
                                       && 
                                      Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                                       && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))))))))))
         ==> M3.UnionFind.Reaches($LS($LZ), this, $ih#d0#0 + 1, $ih#e0#0, $ih#r0#0, $ih#C'0#0));
    $_reverifyPost := false;
}



procedure {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} CheckWellformed$$M3.UnionFind.ExtendedReach_k(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} CheckWellformed$$M3.UnionFind.ExtendedReach_k(this: ref, 
    e#0: ref, 
    C#0: Map Box Box, 
    d0#0: int, 
    d1#0: int, 
    r0#0: ref, 
    r1#0: ref, 
    C'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##C#0: Map Box Box;
  var ##C#1: Map Box Box;
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#2: Map Box Box;
  var ##d#1: int;
  var ##e#1: ref;
  var ##r#1: ref;
  var ##C#3: Map Box Box;

    // AddMethodImpl: ExtendedReach', CheckWellformed$$M3.UnionFind.ExtendedReach_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(279,33): initial state"} true;
    ##C#0 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C#0);
    assume M3.__default.GoodCMap(C#0);
    ##C#1 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#1, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C'#0);
    assume M3.__default.GoodCMap(C'#0);
    assume Map#Domain(C#0)[$Box(r0#0)];
    assume Map#Domain(C#0)[$Box(r1#0)];
    assert Map#Domain(C#0)[$Box(r0#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r0#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
       == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume r0#0 != r1#0;
    assert Map#Domain(C#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert $Is(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1, 
      Tclass._System.nat());
    assume Map#Equal(C'#0, 
      Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
        $Box(r1#0), 
        $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
    assert Map#Domain(C#0)[$Box(r0#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r0#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assume d0#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert Map#Domain(C'#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
    assume d1#0 <= M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
    assume d0#0 < d1#0;
    assume Map#Domain(C#0)[$Box(e#0)];
    ##d#0 := d0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
    ##e#0 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
    ##r#0 := r0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
    ##C#2 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#2, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#2)
       ==> M3.__default.GoodCMap(##C#2)
         || (forall f#0: ref :: 
          { $Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType } 
          $Is(f#0, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#2)[$Box(f#0)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType)
             ==> Map#Domain(##C#2)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#2);
    assert {:subsumption 0} Map#Domain(##C#2)[$Box(##e#0)];
    assume Map#Domain(##C#2)[$Box(##e#0)];
    assume M3.UnionFind.Reaches#canCall(this, d0#0, e#0, r0#0, C#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, d0#0, e#0, r0#0, C#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(285,21): post-state"} true;
    ##d#1 := d1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, Tclass._System.nat(), $Heap);
    ##e#1 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#1, Tclass.M3.Element(), $Heap);
    ##r#1 := r1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#1, Tclass.M3.Element(), $Heap);
    ##C#3 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#3, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#3)
       ==> M3.__default.GoodCMap(##C#3)
         || (forall f#1: ref :: 
          { $Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType } 
          $Is(f#1, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#3)[$Box(f#1)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType)
             ==> Map#Domain(##C#3)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#3);
    assert {:subsumption 0} Map#Domain(##C#3)[$Box(##e#1)];
    assume Map#Domain(##C#3)[$Box(##e#1)];
    assume M3.UnionFind.Reaches#canCall(this, d1#0, e#0, r1#0, C'#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, d1#0, e#0, r1#0, C'#0);
}



procedure {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} Call$$M3.UnionFind.ExtendedReach_k(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#2: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType } 
        $Is(f#2, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#2)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType))]);
  requires M3.__default.GoodCMap#canCall(C'#0)
     ==> M3.__default.GoodCMap(C'#0)
       || (forall f#3: ref :: 
        { $Unbox(Map#Elements(C'#0)[$Box(f#3)]): DatatypeType } 
        $Is(f#3, Tclass.M3.Element?())
           ==> 
          Map#Domain(C'#0)[$Box(f#3)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#3)]): DatatypeType)
           ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#3)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
     == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires r0#0 != r1#0;
  requires Map#Equal(C'#0, 
    Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
      $Box(r1#0), 
      $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires d0#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires d1#0 <= M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
  requires d0#0 < d1#0;
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d0#0, e#0, r0#0, C#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d1#0, e#0, r1#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d1#0, e#0, r1#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} Impl$$M3.UnionFind.ExtendedReach_k(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#4: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType } 
      $Is(f#4, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#4)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType))]);
  free requires M3.__default.GoodCMap#canCall(C'#0)
     && 
    M3.__default.GoodCMap(C'#0)
     && (forall f#5: ref :: 
      { $Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType } 
      $Is(f#5, Tclass.M3.Element?())
         ==> 
        Map#Domain(C'#0)[$Box(f#5)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType)
         ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
     == M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires r0#0 != r1#0;
  requires Map#Equal(C'#0, 
    Map#Build(Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))), 
      $Box(r1#0), 
      $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType) + 1))));
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires d0#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires d1#0 <= M3.Contents.depth($Unbox(Map#Elements(C'#0)[$Box(r1#0)]): DatatypeType);
  requires d0#0 < d1#0;
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d0#0, e#0, r0#0, C#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d1#0, e#0, r1#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d1#0, e#0, r1#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} Impl$$M3.UnionFind.ExtendedReach_k(this: ref, 
    e#0: ref, 
    C#0: Map Box Box, 
    d0#0: int, 
    d1#0: int, 
    r0#0: ref, 
    r1#0: ref, 
    C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#1#0_0: ref;
  var next#0_0: ref;
  var let#0_0#0#0: ref;
  var e##0_0: ref;
  var C##0_0: Map Box Box;
  var d0##0_0: int;
  var d1##0_0: int;
  var r0##0_0: ref;
  var r1##0_0: ref;
  var C'##0_0: Map Box Box;
  var _mcc#0#1_0: int;

    // AddMethodImpl: ExtendedReach', Impl$$M3.UnionFind.ExtendedReach_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(286,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#e0#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#d00#0: int, 
        $ih#d10#0: int, 
        $ih#r00#0: ref, 
        $ih#r10#0: ref, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && $Is($ih#e0#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && LitInt(0) <= $ih#d00#0
           && LitInt(0) <= $ih#d10#0
           && $Is($ih#r00#0, Tclass.M3.Element())
           && $Is($ih#r10#0, Tclass.M3.Element())
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && M3.__default.GoodCMap($ih#C'0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#r00#0)]
           && Map#Domain($ih#C0#0)[$Box($ih#r10#0)]
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
             == M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && $ih#r00#0 != $ih#r10#0
           && Map#Equal($ih#C'0#0, 
            Map#Build(Map#Build($ih#C0#0, $Box($ih#r00#0), $Box(#M3.Contents.Link($ih#r10#0))), 
              $Box($ih#r10#0), 
              $Box(#M3.Contents.Root(M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
                     + 1))))
           && 
          M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && $ih#d00#0
             <= M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && $ih#d10#0
             <= M3.Contents.depth($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#r10#0)]): DatatypeType)
           && $ih#d00#0 < $ih#d10#0
           && 
          Map#Domain($ih#C0#0)[$Box($ih#e0#0)]
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#d00#0, $ih#e0#0, $ih#r00#0, $ih#C0#0)
           && (($ih#e0#0 == null && e#0 != null)
             || (($ih#e0#0 != null <==> e#0 != null)
               && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                   && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                 || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                   && ((0 <= $ih#d00#0 && $ih#d00#0 < d0#0)
                     || ($ih#d00#0 == d0#0
                       && ((0 <= $ih#d10#0 && $ih#d10#0 < d1#0)
                         || ($ih#d10#0 == d1#0
                           && (($ih#r00#0 == null && r0#0 != null)
                             || (($ih#r00#0 != null <==> r0#0 != null)
                               && (($ih#r10#0 == null && r1#0 != null)
                                 || (($ih#r10#0 != null <==> r1#0 != null)
                                   && 
                                  Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                                   && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))))))))
         ==> M3.UnionFind.Reaches($LS($LZ), this, $ih#d10#0, $ih#e0#0, $ih#r10#0, $ih#C'0#0));
    $_reverifyPost := false;
    assert Map#Domain(C#0)[$Box(e#0)];
    assume true;
    havoc _mcc#1#0_0;
    havoc _mcc#0#1_0;
    if ($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType
       == #M3.Contents.Root(_mcc#0#1_0))
    {
        assume LitInt(0) <= _mcc#0#1_0;
    }
    else if ($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType
       == #M3.Contents.Link(_mcc#1#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass.M3.Element());
        havoc next#0_0;
        assume $Is(next#0_0, Tclass.M3.Element?())
           && $IsAlloc(next#0_0, Tclass.M3.Element?(), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass.M3.Element?());
        assume next#0_0 == let#0_0#0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(290,23)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(next#0_0, Tclass.M3.Element());
        e##0_0 := next#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##0_0 := C#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(d0#0 - 1, Tclass._System.nat());
        d0##0_0 := d0#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(d1#0 - 1, Tclass._System.nat());
        d1##0_0 := d1#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r0##0_0 := r0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r1##0_0 := r1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C'##0_0 := C'#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= d0#0
           || (e##0_0 == null && e#0 != null)
           || (Set#Subset(Map#Domain(C##0_0), Map#Domain(C#0))
             && !Set#Subset(Map#Domain(C#0), Map#Domain(C##0_0)))
           || d0##0_0 == d0#0;
        assert 0 <= d1#0
           || (e##0_0 == null && e#0 != null)
           || (Set#Subset(Map#Domain(C##0_0), Map#Domain(C#0))
             && !Set#Subset(Map#Domain(C#0), Map#Domain(C##0_0)))
           || d0##0_0 < d0#0
           || d1##0_0 == d1#0;
        assert (e##0_0 == null && e#0 != null)
           || ((e##0_0 != null <==> e#0 != null)
             && ((Set#Subset(Map#Domain(C##0_0), Map#Domain(C#0))
                 && !Set#Subset(Map#Domain(C#0), Map#Domain(C##0_0)))
               || (Set#Equal(Map#Domain(C##0_0), Map#Domain(C#0))
                 && (d0##0_0 < d0#0
                   || (d0##0_0 == d0#0
                     && (d1##0_0 < d1#0
                       || (d1##0_0 == d1#0
                         && ((r0##0_0 == null && r0#0 != null)
                           || ((r0##0_0 != null <==> r0#0 != null)
                             && ((r1##0_0 == null && r1#0 != null)
                               || ((r1##0_0 != null <==> r1#0 != null)
                                 && 
                                Set#Subset(Map#Domain(C'##0_0), Map#Domain(C'#0))
                                 && !Set#Subset(Map#Domain(C'#0), Map#Domain(C'##0_0)))))))))))));
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.ExtendedReach_k(this, e##0_0, C##0_0, d0##0_0, d1##0_0, r0##0_0, r1##0_0, C'##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(290,55)"} true;
    }
    else
    {
        assume false;
    }
}



procedure {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} CheckWellformed$$M3.UnionFind.JoinMaintainsReaches0(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} CheckWellformed$$M3.UnionFind.JoinMaintainsReaches0(this: ref, r0#0: ref, r1#0: ref, C#0: Map Box Box, C'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##C#0: Map Box Box;
  var ##C#1: Map Box Box;
  var d#0: int;
  var e#0: ref;
  var r#0: ref;
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#2: Map Box Box;
  var ##d#1: int;
  var ##e#1: ref;
  var ##r#1: ref;
  var ##C#3: Map Box Box;
  var e#2: ref;
  var ##d#2: int;
  var ##e#2: ref;
  var ##r#2: ref;
  var ##C#4: Map Box Box;
  var ##d#3: int;
  var ##e#3: ref;
  var ##r#3: ref;
  var ##C#5: Map Box Box;

    // AddMethodImpl: JoinMaintainsReaches0, CheckWellformed$$M3.UnionFind.JoinMaintainsReaches0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(293,33): initial state"} true;
    ##C#0 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C#0);
    assume M3.__default.GoodCMap(C#0);
    assume Map#Domain(C#0)[$Box(r0#0)];
    assume Map#Domain(C#0)[$Box(r1#0)];
    assert Map#Domain(C#0)[$Box(r0#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r0#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
       < M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume Map#Equal(C'#0, Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))));
    ##C#1 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#1, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C'#0);
    assume M3.__default.GoodCMap(C'#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(298,14): post-state"} true;
    havoc d#0;
    havoc e#0;
    havoc r#0;
    assume LitInt(0) <= d#0
       && $Is(e#0, Tclass.M3.Element())
       && $Is(r#0, Tclass.M3.Element());
    if (*)
    {
        assume Map#Domain(C#0)[$Box(e#0)];
        ##d#0 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
        ##e#0 := e#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
        ##r#0 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
        ##C#2 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#2, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#2)
           ==> M3.__default.GoodCMap(##C#2)
             || (forall f#0: ref :: 
              { $Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType } 
              $Is(f#0, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#2)[$Box(f#0)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType)
                 ==> Map#Domain(##C#2)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#2);
        assert {:subsumption 0} Map#Domain(##C#2)[$Box(##e#0)];
        assume Map#Domain(##C#2)[$Box(##e#0)];
        assume M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C#0);
        assume M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C#0);
        assume r#0 != r0#0;
        ##d#1 := d#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#1, Tclass._System.nat(), $Heap);
        ##e#1 := e#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#1, Tclass.M3.Element(), $Heap);
        ##r#1 := r#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#1, Tclass.M3.Element(), $Heap);
        ##C#3 := C'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#3, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#3)
           ==> M3.__default.GoodCMap(##C#3)
             || (forall f#1: ref :: 
              { $Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType } 
              $Is(f#1, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#3)[$Box(f#1)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType)
                 ==> Map#Domain(##C#3)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#3);
        assert {:subsumption 0} Map#Domain(##C#3)[$Box(##e#1)];
        assume Map#Domain(##C#3)[$Box(##e#1)];
        assume M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
        assume M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C'#0);
    }
    else
    {
        assume Map#Domain(C#0)[$Box(e#0)]
             && M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C#0)
             && r#0 != r0#0
           ==> M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C'#0);
    }

    assume (forall d#1: int, e#1: ref, r#1: ref :: 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
        { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
      LitInt(0) <= d#1
           && $Is(e#1, Tclass.M3.Element())
           && $Is(r#1, Tclass.M3.Element())
         ==> 
        Map#Domain(C#0)[$Box(e#1)]
           && M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
           && r#1 != r0#0
         ==> M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0));
    havoc e#2;
    assume $Is(e#2, Tclass.M3.Element());
    if (*)
    {
        assume Map#Domain(C#0)[$Box(e#2)];
        assert Map#Domain(C#0)[$Box(r0#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        ##d#2 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#2, Tclass._System.nat(), $Heap);
        ##e#2 := e#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#2, Tclass.M3.Element(), $Heap);
        ##r#2 := r0#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#2, Tclass.M3.Element(), $Heap);
        ##C#4 := C#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#4, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#4)
           ==> M3.__default.GoodCMap(##C#4)
             || (forall f#2: ref :: 
              { $Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType } 
              $Is(f#2, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#4)[$Box(f#2)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType)
                 ==> Map#Domain(##C#4)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#4);
        assert {:subsumption 0} Map#Domain(##C#4)[$Box(##e#2)];
        assume Map#Domain(##C#4)[$Box(##e#2)];
        assume M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#2, 
          r0#0, 
          C#0);
        assume M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#2, 
          r0#0, 
          C#0);
        assert Map#Domain(C#0)[$Box(r1#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
        ##d#3 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
        // assume allocatedness for argument to function
        assume $IsAlloc(##d#3, Tclass._System.nat(), $Heap);
        ##e#3 := e#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##e#3, Tclass.M3.Element(), $Heap);
        ##r#3 := r1#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##r#3, Tclass.M3.Element(), $Heap);
        ##C#5 := C'#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##C#5, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
        assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#5)
           ==> M3.__default.GoodCMap(##C#5)
             || (forall f#3: ref :: 
              { $Unbox(Map#Elements(##C#5)[$Box(f#3)]): DatatypeType } 
              $Is(f#3, Tclass.M3.Element?())
                 ==> 
                Map#Domain(##C#5)[$Box(f#3)]
                   && M3.Contents.Link_q($Unbox(Map#Elements(##C#5)[$Box(f#3)]): DatatypeType)
                 ==> Map#Domain(##C#5)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#5)[$Box(f#3)]): DatatypeType))]);
        assume M3.__default.GoodCMap(##C#5);
        assert {:subsumption 0} Map#Domain(##C#5)[$Box(##e#3)];
        assume Map#Domain(##C#5)[$Box(##e#3)];
        assume M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#2, 
          r1#0, 
          C'#0);
        assume M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#2, 
          r1#0, 
          C'#0);
    }
    else
    {
        assume Map#Domain(C#0)[$Box(e#2)]
             && M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
              e#2, 
              r0#0, 
              C#0)
           ==> M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
            e#2, 
            r1#0, 
            C'#0);
    }

    assume (forall e#3: ref :: 
      { M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#3, 
          r1#0, 
          C'#0) } 
        { M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0) } 
        { Map#Domain(C#0)[$Box(e#3)] } 
      $Is(e#3, Tclass.M3.Element())
         ==> 
        Map#Domain(C#0)[$Box(e#3)]
           && M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#3, 
            r0#0, 
            C#0)
         ==> M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#3, 
          r1#0, 
          C'#0));
}



procedure {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} Call$$M3.UnionFind.JoinMaintainsReaches0(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#4: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType } 
        $Is(f#4, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#4)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
     < M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))));
  requires M3.__default.GoodCMap#canCall(C'#0)
     ==> M3.__default.GoodCMap(C'#0)
       || (forall f#5: ref :: 
        { $Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType } 
        $Is(f#5, Tclass.M3.Element?())
           ==> 
          Map#Domain(C'#0)[$Box(f#5)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType)
           ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
       ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C#0)
         && (M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
           ==> 
          r#1 != r0#0
           ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C'#0)));
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
         && M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
         && r#1 != r0#0
       ==> M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0));
  free ensures (forall e#3: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
        e#3, 
        r0#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#3)] } 
    $Is(e#3, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#3)]
       ==> M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0)
         && (M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#3, 
            r0#0, 
            C#0)
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
            e#3, 
            r1#0, 
            C'#0)));
  free ensures (forall e#3: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
        e#3, 
        r0#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#3)] } 
    $Is(e#3, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#3)]
         && M3.UnionFind.Reaches($LS($LZ), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0)
       ==> M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} Impl$$M3.UnionFind.JoinMaintainsReaches0(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#6: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType } 
      $Is(f#6, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#6)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType)
     < M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))));
  free requires M3.__default.GoodCMap#canCall(C'#0)
     && 
    M3.__default.GoodCMap(C'#0)
     && (forall f#7: ref :: 
      { $Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType } 
      $Is(f#7, Tclass.M3.Element?())
         ==> 
        Map#Domain(C'#0)[$Box(f#7)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType)
         ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
       ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C#0)
         && (M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
           ==> 
          r#1 != r0#0
           ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C'#0)));
  ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
         && M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C#0)
         && r#1 != r0#0
       ==> M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C'#0));
  free ensures (forall e#3: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
        e#3, 
        r0#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#3)] } 
    $Is(e#3, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#3)]
       ==> M3.UnionFind.Reaches#canCall(this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0)
         && (M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#3, 
            r0#0, 
            C#0)
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
            e#3, 
            r1#0, 
            C'#0)));
  ensures (forall e#3: ref :: 
    { M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0) } 
      { M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
        e#3, 
        r0#0, 
        C#0) } 
      { Map#Domain(C#0)[$Box(e#3)] } 
    $Is(e#3, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#3)]
         && M3.UnionFind.Reaches($LS($LS($LZ)), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
          e#3, 
          r0#0, 
          C#0)
       ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
        this, 
        M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
        e#3, 
        r1#0, 
        C'#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, r0#0, r1#0, C#0, C'#0} Impl$$M3.UnionFind.JoinMaintainsReaches0(this: ref, r0#0: ref, r1#0: ref, C#0: Map Box Box, C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var d#3: int;
  var e#6: ref;
  var r#3: ref;
  var ##d#4: int;
  var ##e#4: ref;
  var ##r#4: ref;
  var ##C#6: Map Box Box;
  var d##0: int;
  var e##0: ref;
  var r##0: ref;
  var C##0: Map Box Box;
  var td##0: int;
  var tt##0: ref;
  var tm##0: ref;
  var C'##0: Map Box Box;
  var e#8: ref;
  var ##d#5: int;
  var ##e#5: ref;
  var ##r#5: ref;
  var ##C#7: Map Box Box;
  var e##1: ref;
  var C##1: Map Box Box;
  var d0##0: int;
  var d1##0: int;
  var r0##0: ref;
  var r1##0: ref;
  var C'##1: Map Box Box;

    // AddMethodImpl: JoinMaintainsReaches0, Impl$$M3.UnionFind.JoinMaintainsReaches0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(300,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#r00#0: ref, 
        $ih#r10#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && $Is($ih#r00#0, Tclass.M3.Element())
           && $Is($ih#r10#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#r00#0)]
           && Map#Domain($ih#C0#0)[$Box($ih#r10#0)]
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
             < M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && Map#Equal($ih#C'0#0, 
            Map#Build($ih#C0#0, $Box($ih#r00#0), $Box(#M3.Contents.Link($ih#r10#0))))
           && M3.__default.GoodCMap($ih#C'0#0)
           && (($ih#r00#0 == null && r0#0 != null)
             || (($ih#r00#0 != null <==> r0#0 != null)
               && (($ih#r10#0 == null && r1#0 != null)
                 || (($ih#r10#0 != null <==> r1#0 != null)
                   && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                       && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                     || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                       && 
                      Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                       && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))
         ==> (forall d#2: int, e#4: ref, r#2: ref :: 
            { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#4, r#2, $ih#C'0#0) } 
              { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#4, r#2, $ih#C0#0) } 
            LitInt(0) <= d#2
                 && $Is(e#4, Tclass.M3.Element())
                 && $Is(r#2, Tclass.M3.Element())
               ==> 
              Map#Domain($ih#C0#0)[$Box(e#4)]
                 && M3.UnionFind.Reaches($LS($LZ), this, d#2, e#4, r#2, $ih#C0#0)
                 && r#2 != $ih#r00#0
               ==> M3.UnionFind.Reaches($LS($LZ), this, d#2, e#4, r#2, $ih#C'0#0))
           && (forall e#5: ref :: 
            { M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType), 
                e#5, 
                $ih#r10#0, 
                $ih#C'0#0) } 
              { M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType), 
                e#5, 
                $ih#r00#0, 
                $ih#C0#0) } 
              { Map#Domain($ih#C0#0)[$Box(e#5)] } 
            $Is(e#5, Tclass.M3.Element())
               ==> 
              Map#Domain($ih#C0#0)[$Box(e#5)]
                 && M3.UnionFind.Reaches($LS($LZ), 
                  this, 
                  M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType), 
                  e#5, 
                  $ih#r00#0, 
                  $ih#C0#0)
               ==> M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType), 
                e#5, 
                $ih#r10#0, 
                $ih#C'0#0)));
    $_reverifyPost := false;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(301,7)
    if (*)
    {
        // Assume Fuel Constant
        havoc d#3, e#6, r#3;
        assume LitInt(0) <= d#3
           && $Is(e#6, Tclass.M3.Element())
           && $Is(r#3, Tclass.M3.Element());
        if (Map#Domain(C#0)[$Box(e#6)])
        {
            ##d#4 := d#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#4, Tclass._System.nat(), $Heap);
            ##e#4 := e#6;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#4, Tclass.M3.Element(), $Heap);
            ##r#4 := r#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#4, Tclass.M3.Element(), $Heap);
            ##C#6 := C#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#6, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
            assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#6)
               ==> M3.__default.GoodCMap(##C#6)
                 || (forall f#8: ref :: 
                  { $Unbox(Map#Elements(##C#6)[$Box(f#8)]): DatatypeType } 
                  $Is(f#8, Tclass.M3.Element?())
                     ==> 
                    Map#Domain(##C#6)[$Box(f#8)]
                       && M3.Contents.Link_q($Unbox(Map#Elements(##C#6)[$Box(f#8)]): DatatypeType)
                     ==> Map#Domain(##C#6)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#6)[$Box(f#8)]): DatatypeType))]);
            assert {:subsumption 0} Map#Domain(##C#6)[$Box(##e#4)];
            assume M3.UnionFind.Reaches#canCall(this, d#3, e#6, r#3, C#0);
        }

        if (Map#Domain(C#0)[$Box(e#6)]
           && M3.UnionFind.Reaches($LS($LZ), this, d#3, e#6, r#3, C#0))
        {
        }

        assume Map#Domain(C#0)[$Box(e#6)]
           ==> M3.UnionFind.Reaches#canCall(this, d#3, e#6, r#3, C#0);
        assume Map#Domain(C#0)[$Box(e#6)]
           && M3.UnionFind.Reaches($LS($LZ), this, d#3, e#6, r#3, C#0)
           && r#3 != r0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(304,40)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0 := d#3;
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##0 := e#6;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r##0 := r#3;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##0 := C#0;
        assert Map#Domain(C#0)[$Box(r0#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        td##0 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        tt##0 := r0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        tm##0 := r1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C'##0 := C'#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.ReachUnaffectedByChangeFromRoot(this, d##0, e##0, r##0, C##0, td##0, tt##0, tm##0, C'##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(304,76)"} true;
        assert M3.UnionFind.Reaches($LS($LS($LZ)), this, d#3, e#6, r#3, C'#0);
        assume false;
    }
    else
    {
        assume (forall d#4: int, e#7: ref, r#4: ref :: 
          { M3.UnionFind.Reaches($LS($LZ), this, d#4, e#7, r#4, C'#0) } 
            { M3.UnionFind.Reaches($LS($LZ), this, d#4, e#7, r#4, C#0) } 
          LitInt(0) <= d#4
               && $Is(e#7, Tclass.M3.Element())
               && $Is(r#4, Tclass.M3.Element())
               && 
              Map#Domain(C#0)[$Box(e#7)]
               && M3.UnionFind.Reaches($LS($LZ), this, d#4, e#7, r#4, C#0)
               && r#4 != r0#0
             ==> M3.UnionFind.Reaches($LS($LZ), this, d#4, e#7, r#4, C'#0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(305,6)"} true;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(306,7)
    if (*)
    {
        // Assume Fuel Constant
        havoc e#8;
        assume $Is(e#8, Tclass.M3.Element());
        if (Map#Domain(C#0)[$Box(e#8)])
        {
            assert {:subsumption 0} Map#Domain(C#0)[$Box(r0#0)];
            assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
            ##d#5 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#5, Tclass._System.nat(), $Heap);
            ##e#5 := e#8;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#5, Tclass.M3.Element(), $Heap);
            ##r#5 := r0#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#5, Tclass.M3.Element(), $Heap);
            ##C#7 := C#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#7, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
            assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#7)
               ==> M3.__default.GoodCMap(##C#7)
                 || (forall f#9: ref :: 
                  { $Unbox(Map#Elements(##C#7)[$Box(f#9)]): DatatypeType } 
                  $Is(f#9, Tclass.M3.Element?())
                     ==> 
                    Map#Domain(##C#7)[$Box(f#9)]
                       && M3.Contents.Link_q($Unbox(Map#Elements(##C#7)[$Box(f#9)]): DatatypeType)
                     ==> Map#Domain(##C#7)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#7)[$Box(f#9)]): DatatypeType))]);
            assert {:subsumption 0} Map#Domain(##C#7)[$Box(##e#5)];
            assume M3.UnionFind.Reaches#canCall(this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
              e#8, 
              r0#0, 
              C#0);
        }

        assume Map#Domain(C#0)[$Box(e#8)]
           ==> M3.UnionFind.Reaches#canCall(this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#8, 
            r0#0, 
            C#0);
        assume Map#Domain(C#0)[$Box(e#8)]
           && M3.UnionFind.Reaches($LS($LZ), 
            this, 
            M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
            e#8, 
            r0#0, 
            C#0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(309,22)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##1 := e#8;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##1 := C#0;
        assert Map#Domain(C#0)[$Box(r0#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        d0##0 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
        assert Map#Domain(C#0)[$Box(r1#0)];
        assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        d1##0 := M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
        assume true;
        // ProcessCallStmt: CheckSubrange
        r0##0 := r0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r1##0 := r1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C'##1 := C'#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.ExtendedReach(this, e##1, C##1, d0##0, d1##0, r0##0, r1##0, C'##1);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(309,65)"} true;
        assert M3.UnionFind.Reaches($LS($LS($LZ)), 
          this, 
          M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
          e#8, 
          r1#0, 
          C'#0);
        assume false;
    }
    else
    {
        assume (forall e#9: ref :: 
          { M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
              e#9, 
              r1#0, 
              C'#0) } 
            { M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
              e#9, 
              r0#0, 
              C#0) } 
            { Map#Domain(C#0)[$Box(e#9)] } 
          $Is(e#9, Tclass.M3.Element())
               && 
              Map#Domain(C#0)[$Box(e#9)]
               && M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType), 
                e#9, 
                r0#0, 
                C#0)
             ==> M3.UnionFind.Reaches($LS($LZ), 
              this, 
              M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType), 
              e#9, 
              r1#0, 
              C'#0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(310,6)"} true;
}



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, C'#0} CheckWellformed$$M3.UnionFind.ReachUnaffectedByChangeFromRoot(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, C'#0} CheckWellformed$$M3.UnionFind.ReachUnaffectedByChangeFromRoot(this: ref, 
    d#0: int, 
    e#0: ref, 
    r#0: ref, 
    C#0: Map Box Box, 
    td#0: int, 
    tt#0: ref, 
    tm#0: ref, 
    C'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##C#0: Map Box Box;
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#1: Map Box Box;
  var ##d#1: int;
  var ##e#1: ref;
  var ##r#1: ref;
  var ##C#2: Map Box Box;
  var ##C#3: Map Box Box;
  var ##d#2: int;
  var ##e#2: ref;
  var ##r#2: ref;
  var ##C#4: Map Box Box;

    // AddMethodImpl: ReachUnaffectedByChangeFromRoot, CheckWellformed$$M3.UnionFind.ReachUnaffectedByChangeFromRoot
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(313,33): initial state"} true;
    ##C#0 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C#0);
    assume M3.__default.GoodCMap(C#0);
    assume Map#Domain(C#0)[$Box(e#0)];
    ##d#0 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
    ##e#0 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
    ##r#0 := r#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
    ##C#1 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#1, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#1)
       ==> M3.__default.GoodCMap(##C#1)
         || (forall f#0: ref :: 
          { $Unbox(Map#Elements(##C#1)[$Box(f#0)]): DatatypeType } 
          $Is(f#0, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#1)[$Box(f#0)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#1)[$Box(f#0)]): DatatypeType)
             ==> Map#Domain(##C#1)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#1)[$Box(f#0)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#1);
    assert {:subsumption 0} Map#Domain(##C#1)[$Box(##e#0)];
    assume Map#Domain(##C#1)[$Box(##e#0)];
    assume M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C#0);
    assume Map#Domain(C#0)[$Box(tt#0)];
    ##d#1 := td#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, Tclass._System.nat(), $Heap);
    ##e#1 := tt#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#1, Tclass.M3.Element(), $Heap);
    ##r#1 := tt#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#1, Tclass.M3.Element(), $Heap);
    ##C#2 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#2, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#2)
       ==> M3.__default.GoodCMap(##C#2)
         || (forall f#1: ref :: 
          { $Unbox(Map#Elements(##C#2)[$Box(f#1)]): DatatypeType } 
          $Is(f#1, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#2)[$Box(f#1)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#2)[$Box(f#1)]): DatatypeType)
             ==> Map#Domain(##C#2)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#2)[$Box(f#1)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#2);
    assert {:subsumption 0} Map#Domain(##C#2)[$Box(##e#1)];
    assume Map#Domain(##C#2)[$Box(##e#1)];
    assume M3.UnionFind.Reaches#canCall(this, td#0, tt#0, tt#0, C#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, td#0, tt#0, tt#0, C#0);
    assume tt#0 != r#0;
    assert Map#Domain(C#0)[$Box(tt#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(tt#0)]): DatatypeType);
    assume Map#Equal(C'#0, Map#Build(C#0, $Box(tt#0), $Box(#M3.Contents.Link(tm#0))));
    ##C#3 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#3, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C'#0);
    assume M3.__default.GoodCMap(C'#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(319,21): post-state"} true;
    ##d#2 := d#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#2, Tclass._System.nat(), $Heap);
    ##e#2 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#2, Tclass.M3.Element(), $Heap);
    ##r#2 := r#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#2, Tclass.M3.Element(), $Heap);
    ##C#4 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#4, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#4)
       ==> M3.__default.GoodCMap(##C#4)
         || (forall f#2: ref :: 
          { $Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType } 
          $Is(f#2, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#4)[$Box(f#2)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType)
             ==> Map#Domain(##C#4)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#4)[$Box(f#2)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#4);
    assert {:subsumption 0} Map#Domain(##C#4)[$Box(##e#2)];
    assume Map#Domain(##C#4)[$Box(##e#2)];
    assume M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, d#0, e#0, r#0, C'#0);
}



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, C'#0} Call$$M3.UnionFind.ReachUnaffectedByChangeFromRoot(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#3: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType } 
        $Is(f#3, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#3)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C#0);
  requires Map#Domain(C#0)[$Box(tt#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, td#0, tt#0, tt#0, C#0);
  requires tt#0 != r#0;
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(tt#0)]): DatatypeType);
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(tt#0), $Box(#M3.Contents.Link(tm#0))));
  requires M3.__default.GoodCMap#canCall(C'#0)
     ==> M3.__default.GoodCMap(C'#0)
       || (forall f#4: ref :: 
        { $Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType } 
        $Is(f#4, Tclass.M3.Element?())
           ==> 
          Map#Domain(C'#0)[$Box(f#4)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType)
           ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, C'#0} Impl$$M3.UnionFind.ReachUnaffectedByChangeFromRoot(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 10 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#5: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType } 
      $Is(f#5, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#5)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C#0);
  requires Map#Domain(C#0)[$Box(tt#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, td#0, tt#0, tt#0, C#0);
  requires tt#0 != r#0;
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(tt#0)]): DatatypeType);
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(tt#0), $Box(#M3.Contents.Link(tm#0))));
  free requires M3.__default.GoodCMap#canCall(C'#0)
     && 
    M3.__default.GoodCMap(C'#0)
     && (forall f#6: ref :: 
      { $Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType } 
      $Is(f#6, Tclass.M3.Element?())
         ==> 
        Map#Domain(C'#0)[$Box(f#6)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType)
         ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, C'#0} Impl$$M3.UnionFind.ReachUnaffectedByChangeFromRoot(this: ref, 
    d#0: int, 
    e#0: ref, 
    r#0: ref, 
    C#0: Map Box Box, 
    td#0: int, 
    tt#0: ref, 
    tm#0: ref, 
    C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: ReachUnaffectedByChangeFromRoot, Impl$$M3.UnionFind.ReachUnaffectedByChangeFromRoot
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(320,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#d0#0: int, 
        $ih#e0#0: ref, 
        $ih#r0#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#td0#0: int, 
        $ih#tt0#0: ref, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && LitInt(0) <= $ih#d0#0
           && $Is($ih#e0#0, Tclass.M3.Element())
           && $Is($ih#r0#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && LitInt(0) <= $ih#td0#0
           && $Is($ih#tt0#0, Tclass.M3.Element())
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#e0#0)]
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#d0#0, $ih#e0#0, $ih#r0#0, $ih#C0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#tt0#0)]
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#td0#0, $ih#tt0#0, $ih#tt0#0, $ih#C0#0)
           && $ih#tt0#0 != $ih#r0#0
           && 
          M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#tt0#0)]): DatatypeType)
           && Map#Equal($ih#C'0#0, Map#Build($ih#C0#0, $Box($ih#tt0#0), $Box(#M3.Contents.Link(tm#0))))
           && M3.__default.GoodCMap($ih#C'0#0)
           && ((0 <= $ih#d0#0 && $ih#d0#0 < d#0)
             || ($ih#d0#0 == d#0
               && (($ih#e0#0 == null && e#0 != null)
                 || (($ih#e0#0 != null <==> e#0 != null)
                   && (($ih#r0#0 == null && r#0 != null)
                     || (($ih#r0#0 != null <==> r#0 != null)
                       && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                         || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && ((0 <= $ih#td0#0 && $ih#td0#0 < td#0)
                             || ($ih#td0#0 == td#0
                               && (($ih#tt0#0 == null && tt#0 != null)
                                 || (($ih#tt0#0 != null <==> tt#0 != null)
                                   && ((tm#0 == null && tm#0 != null)
                                     || ((tm#0 != null <==> tm#0 != null)
                                       && 
                                      Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                                       && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))))))))))
         ==> M3.UnionFind.Reaches($LS($LZ), this, $ih#d0#0, $ih#e0#0, $ih#r0#0, $ih#C'0#0));
    $_reverifyPost := false;
}



procedure {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} CheckWellformed$$M3.UnionFind.ExtendedReach(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} CheckWellformed$$M3.UnionFind.ExtendedReach(this: ref, 
    e#0: ref, 
    C#0: Map Box Box, 
    d0#0: int, 
    d1#0: int, 
    r0#0: ref, 
    r1#0: ref, 
    C'#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##C#0: Map Box Box;
  var ##C#1: Map Box Box;
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#2: Map Box Box;
  var ##d#1: int;
  var ##e#1: ref;
  var ##r#1: ref;
  var ##C#3: Map Box Box;

    // AddMethodImpl: ExtendedReach, CheckWellformed$$M3.UnionFind.ExtendedReach
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(323,33): initial state"} true;
    ##C#0 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C#0);
    assume M3.__default.GoodCMap(C#0);
    ##C#1 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#1, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume M3.__default.GoodCMap#canCall(C'#0);
    assume M3.__default.GoodCMap(C'#0);
    assume Map#Domain(C#0)[$Box(r0#0)];
    assume Map#Domain(C#0)[$Box(r1#0)];
    assume r0#0 != r1#0;
    assume Map#Equal(C'#0, Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))));
    assert Map#Domain(C#0)[$Box(r0#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r0#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assume d0#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assume M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assert Map#Domain(C#0)[$Box(r1#0)];
    assert M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume d1#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
    assume d0#0 < d1#0;
    assume Map#Domain(C#0)[$Box(e#0)];
    ##d#0 := d0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
    ##e#0 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
    ##r#0 := r0#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
    ##C#2 := C#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#2, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#2)
       ==> M3.__default.GoodCMap(##C#2)
         || (forall f#0: ref :: 
          { $Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType } 
          $Is(f#0, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#2)[$Box(f#0)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType)
             ==> Map#Domain(##C#2)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#2)[$Box(f#0)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#2);
    assert {:subsumption 0} Map#Domain(##C#2)[$Box(##e#0)];
    assume Map#Domain(##C#2)[$Box(##e#0)];
    assume M3.UnionFind.Reaches#canCall(this, d0#0, e#0, r0#0, C#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, d0#0, e#0, r0#0, C#0);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(329,21): post-state"} true;
    ##d#1 := d1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, Tclass._System.nat(), $Heap);
    ##e#1 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#1, Tclass.M3.Element(), $Heap);
    ##r#1 := r1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#1, Tclass.M3.Element(), $Heap);
    ##C#3 := C'#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#3, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assert {:subsumption 0} M3.__default.GoodCMap#canCall(##C#3)
       ==> M3.__default.GoodCMap(##C#3)
         || (forall f#1: ref :: 
          { $Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType } 
          $Is(f#1, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#3)[$Box(f#1)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType)
             ==> Map#Domain(##C#3)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#3)[$Box(f#1)]): DatatypeType))]);
    assume M3.__default.GoodCMap(##C#3);
    assert {:subsumption 0} Map#Domain(##C#3)[$Box(##e#1)];
    assume Map#Domain(##C#3)[$Box(##e#1)];
    assume M3.UnionFind.Reaches#canCall(this, d1#0, e#0, r1#0, C'#0);
    assume M3.UnionFind.Reaches($LS($LZ), this, d1#0, e#0, r1#0, C'#0);
}



procedure {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} Call$$M3.UnionFind.ExtendedReach(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#2: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType } 
        $Is(f#2, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#2)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType))]);
  requires M3.__default.GoodCMap#canCall(C'#0)
     ==> M3.__default.GoodCMap(C'#0)
       || (forall f#3: ref :: 
        { $Unbox(Map#Elements(C'#0)[$Box(f#3)]): DatatypeType } 
        $Is(f#3, Tclass.M3.Element?())
           ==> 
          Map#Domain(C'#0)[$Box(f#3)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#3)]): DatatypeType)
           ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#3)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires r0#0 != r1#0;
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))));
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires d0#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires d1#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires d0#0 < d1#0;
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d0#0, e#0, r0#0, C#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d1#0, e#0, r1#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d1#0, e#0, r1#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} Impl$$M3.UnionFind.ExtendedReach(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 11 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#4: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType } 
      $Is(f#4, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#4)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType))]);
  free requires M3.__default.GoodCMap#canCall(C'#0)
     && 
    M3.__default.GoodCMap(C'#0)
     && (forall f#5: ref :: 
      { $Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType } 
      $Is(f#5, Tclass.M3.Element?())
         ==> 
        Map#Domain(C'#0)[$Box(f#5)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType)
         ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(r0#0)];
  requires Map#Domain(C#0)[$Box(r1#0)];
  requires r0#0 != r1#0;
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(r0#0), $Box(#M3.Contents.Link(r1#0))));
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires d0#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r0#0)]): DatatypeType);
  requires M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires d1#0 <= M3.Contents.depth($Unbox(Map#Elements(C#0)[$Box(r1#0)]): DatatypeType);
  requires d0#0 < d1#0;
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d0#0, e#0, r0#0, C#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d1#0, e#0, r1#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d1#0, e#0, r1#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, e#0, C#0, d0#0, d1#0, r0#0, r1#0, C'#0} Impl$$M3.UnionFind.ExtendedReach(this: ref, 
    e#0: ref, 
    C#0: Map Box Box, 
    d0#0: int, 
    d1#0: int, 
    r0#0: ref, 
    r1#0: ref, 
    C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var _mcc#1#0_0: ref;
  var next#0_0: ref;
  var let#0_0#0#0: ref;
  var e##0_0: ref;
  var C##0_0: Map Box Box;
  var d0##0_0: int;
  var d1##0_0: int;
  var r0##0_0: ref;
  var r1##0_0: ref;
  var C'##0_0: Map Box Box;
  var _mcc#0#1_0: int;

    // AddMethodImpl: ExtendedReach, Impl$$M3.UnionFind.ExtendedReach
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(330,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#e0#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#d00#0: int, 
        $ih#d10#0: int, 
        $ih#r00#0: ref, 
        $ih#r10#0: ref, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && $Is($ih#e0#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && LitInt(0) <= $ih#d00#0
           && LitInt(0) <= $ih#d10#0
           && $Is($ih#r00#0, Tclass.M3.Element())
           && $Is($ih#r10#0, Tclass.M3.Element())
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && M3.__default.GoodCMap($ih#C'0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#r00#0)]
           && Map#Domain($ih#C0#0)[$Box($ih#r10#0)]
           && $ih#r00#0 != $ih#r10#0
           && Map#Equal($ih#C'0#0, 
            Map#Build($ih#C0#0, $Box($ih#r00#0), $Box(#M3.Contents.Link($ih#r10#0))))
           && 
          M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && $ih#d00#0
             <= M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r00#0)]): DatatypeType)
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && $ih#d10#0
             <= M3.Contents.depth($Unbox(Map#Elements($ih#C0#0)[$Box($ih#r10#0)]): DatatypeType)
           && $ih#d00#0 < $ih#d10#0
           && 
          Map#Domain($ih#C0#0)[$Box($ih#e0#0)]
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#d00#0, $ih#e0#0, $ih#r00#0, $ih#C0#0)
           && (($ih#e0#0 == null && e#0 != null)
             || (($ih#e0#0 != null <==> e#0 != null)
               && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                   && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                 || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                   && ((0 <= $ih#d00#0 && $ih#d00#0 < d0#0)
                     || ($ih#d00#0 == d0#0
                       && ((0 <= $ih#d10#0 && $ih#d10#0 < d1#0)
                         || ($ih#d10#0 == d1#0
                           && (($ih#r00#0 == null && r0#0 != null)
                             || (($ih#r00#0 != null <==> r0#0 != null)
                               && (($ih#r10#0 == null && r1#0 != null)
                                 || (($ih#r10#0 != null <==> r1#0 != null)
                                   && 
                                  Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                                   && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))))))))
         ==> M3.UnionFind.Reaches($LS($LZ), this, $ih#d10#0, $ih#e0#0, $ih#r10#0, $ih#C'0#0));
    $_reverifyPost := false;
    assert Map#Domain(C#0)[$Box(e#0)];
    assume true;
    havoc _mcc#1#0_0;
    havoc _mcc#0#1_0;
    if ($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType
       == #M3.Contents.Root(_mcc#0#1_0))
    {
        assume LitInt(0) <= _mcc#0#1_0;
    }
    else if ($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType
       == #M3.Contents.Link(_mcc#1#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass.M3.Element());
        havoc next#0_0;
        assume $Is(next#0_0, Tclass.M3.Element?())
           && $IsAlloc(next#0_0, Tclass.M3.Element?(), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass.M3.Element?());
        assume next#0_0 == let#0_0#0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(334,22)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(next#0_0, Tclass.M3.Element());
        e##0_0 := next#0_0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##0_0 := C#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(d0#0 - 1, Tclass._System.nat());
        d0##0_0 := d0#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(d1#0 - 1, Tclass._System.nat());
        d1##0_0 := d1#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r0##0_0 := r0#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r1##0_0 := r1#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C'##0_0 := C'#0;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assert 0 <= d0#0
           || (e##0_0 == null && e#0 != null)
           || (Set#Subset(Map#Domain(C##0_0), Map#Domain(C#0))
             && !Set#Subset(Map#Domain(C#0), Map#Domain(C##0_0)))
           || d0##0_0 == d0#0;
        assert 0 <= d1#0
           || (e##0_0 == null && e#0 != null)
           || (Set#Subset(Map#Domain(C##0_0), Map#Domain(C#0))
             && !Set#Subset(Map#Domain(C#0), Map#Domain(C##0_0)))
           || d0##0_0 < d0#0
           || d1##0_0 == d1#0;
        assert (e##0_0 == null && e#0 != null)
           || ((e##0_0 != null <==> e#0 != null)
             && ((Set#Subset(Map#Domain(C##0_0), Map#Domain(C#0))
                 && !Set#Subset(Map#Domain(C#0), Map#Domain(C##0_0)))
               || (Set#Equal(Map#Domain(C##0_0), Map#Domain(C#0))
                 && (d0##0_0 < d0#0
                   || (d0##0_0 == d0#0
                     && (d1##0_0 < d1#0
                       || (d1##0_0 == d1#0
                         && ((r0##0_0 == null && r0#0 != null)
                           || ((r0##0_0 != null <==> r0#0 != null)
                             && ((r1##0_0 == null && r1#0 != null)
                               || ((r1##0_0 != null <==> r1#0 != null)
                                 && 
                                Set#Subset(Map#Domain(C'##0_0), Map#Domain(C'#0))
                                 && !Set#Subset(Map#Domain(C'#0), Map#Domain(C'##0_0)))))))))))));
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.ExtendedReach(this, e##0_0, C##0_0, d0##0_0, d1##0_0, r0##0_0, r1##0_0, C'##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy(334,54)"} true;
    }
    else
    {
        assume false;
    }
}



procedure CheckWellformed$$M3.UnionFind.Find(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$M3.UnionFind.Find(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap));
  // user-defined preconditions
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#1: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]): ref } 
            $Is(e#1, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#2: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)] } 
            $Is(e#2, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]): ref));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#3: ref :: 
            { read($Heap, e#3, M3.Element.c) } 
            $Is(e#3, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
                 && M3.Contents.Link_q(read($Heap, e#3, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#3, M3.Element.c)))]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#4: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)] } 
            $Is(e#4, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                        M3.Element.c)), 
                    e#4, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  free ensures M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Map#Equal(read($Heap, this, M3.UnionFind.M), read(old($Heap), this, M3.UnionFind.M));
  ensures $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref == r#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$M3.UnionFind.Find(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap))
   returns (defass#r#0: bool, 
    r#0: ref
       where defass#r#0
         ==> $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    $_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#13: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#13)]): ref } 
            $Is(e#13, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#13)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#13)]]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#14: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#14)] } 
            $Is(e#14, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]): ref));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#15: ref :: 
            { read($Heap, e#15, M3.Element.c) } 
            $Is(e#15, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]
                 && M3.Contents.Link_q(read($Heap, e#15, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#15, M3.Element.c)))]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#16: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)] } 
            $Is(e#16, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref, 
                        M3.Element.c)), 
                    e#16, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  free ensures true;
  ensures $_reverifyPost
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
           && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures $_reverifyPost
     ==> Map#Equal(read($Heap, this, M3.UnionFind.M), read(old($Heap), this, M3.UnionFind.M));
  ensures $_reverifyPost
     ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref == r#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$M3.UnionFind.Find(this: ref, e#0: ref) returns (defass#r#0: bool, r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs##0: ref
     where $Is($rhs##0, Tclass.M3.Element())
       && $IsAlloc($rhs##0, Tclass.M3.Element(), $Heap);
  var d##0: int;
  var e##0: ref;

    // AddMethodImpl: Find, Impl$$M3.UnionFind.Find
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, M3.UnionFind.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](129,4): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](130,19)
    assume true;
    // TrCallStmt: Adding lhs with type Element
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
    assume $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref != null;
    assume M3.Contents.Root_q(read($Heap, 
        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
        M3.Element.c));
    assume true;
    // ProcessCallStmt: CheckSubrange
    d##0 := M3.Contents.depth(read($Heap, 
        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
        M3.Element.c));
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := e#0;
    assume (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$M3.UnionFind.FindAux(this, d##0, e##0);
    // TrCallStmt: After ProcessCallStmt
    r#0 := $rhs##0;
    defass#r#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](130,35)"} true;
    assert defass#r#0;
}



procedure {:_induction this} CheckWellformed$$M3.UnionFind.NextReachesSame(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction this} Call$$M3.UnionFind.NextReachesSame(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap));
  // user-defined preconditions
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#1: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]): ref } 
            $Is(e#1, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#2: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)] } 
            $Is(e#2, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]): ref));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#3: ref :: 
            { read($Heap, e#3, M3.Element.c) } 
            $Is(e#3, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
                 && M3.Contents.Link_q(read($Heap, e#3, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#3, M3.Element.c)))]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#4: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)] } 
            $Is(e#4, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                        M3.Element.c)), 
                    e#4, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
  requires M3.Contents.Link_q(read($Heap, e#0, M3.Element.c));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref
     == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#0, M3.Element.c)))]): ref;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction this} Impl$$M3.UnionFind.NextReachesSame(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
  requires M3.Contents.Link_q(read($Heap, e#0, M3.Element.c));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures $_reverifyPost
     ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref
       == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#0, M3.Element.c)))]): ref;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction this} Impl$$M3.UnionFind.NextReachesSame(this: ref, e#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var next#0: ref
     where $Is(next#0, Tclass.M3.Element()) && $IsAlloc(next#0, Tclass.M3.Element(), $Heap);
  var d0#0: int where LitInt(0) <= d0#0;
  var d1#0: int where LitInt(0) <= d1#0;
  var $rhs#0: int where LitInt(0) <= $rhs#0;
  var $rhs#1: int where LitInt(0) <= $rhs#1;
  var newtype$check#0: int;
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#0: Map Box Box;
  var ##d#1: int;
  var ##e#1: ref;
  var ##r#1: ref;
  var ##C#1: Map Box Box;
  var d0##0: int;
  var d1##0: int;
  var e##0: ref;
  var r0##0: ref;
  var r1##0: ref;
  var C##0: Map Box Box;

    // AddMethodImpl: NextReachesSame, Impl$$M3.UnionFind.NextReachesSame
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](136,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && 
          M3.UnionFind.Valid($initHeapForallStmt#0, $ih#this0#0)
           && 
          Map#Domain(read($initHeapForallStmt#0, $ih#this0#0, M3.UnionFind.M))[$Box(e#0)]
           && M3.Contents.Link_q(read($initHeapForallStmt#0, e#0, M3.Element.c))
           && 
          e#0 == null
           && e#0 != null
         ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref
           == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#0, M3.Element.c)))]): ref);
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](137,16)
    assume true;
    assume e#0 != null;
    assume M3.Contents.Link_q(read($Heap, e#0, M3.Element.c));
    assume true;
    next#0 := M3.Contents.next(read($Heap, e#0, M3.Element.c));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](137,26)"} true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](138,18)
    assume true;
    assume true;
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
    assume $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref != null;
    assume M3.Contents.Root_q(read($Heap, 
        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
        M3.Element.c));
    assume true;
    $rhs#0 := M3.Contents.depth(read($Heap, 
        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
        M3.Element.c));
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(next#0)];
    assume $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(next#0)]): ref
       != null;
    assume M3.Contents.Root_q(read($Heap, 
        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(next#0)]): ref, 
        M3.Element.c));
    assume true;
    $rhs#1 := M3.Contents.depth(read($Heap, 
        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(next#0)]): ref, 
        M3.Element.c));
    d0#0 := $rhs#0;
    d1#0 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](138,49)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](139,7)
    newtype$check#0 := d0#0 - 1;
    assume LitInt(0) <= newtype$check#0;
    assume {:subsumption 0} Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
    assume {:subsumption 0} (forall f#0: ref :: 
      { read($Heap, f#0, M3.Element.c) } 
      $Is(f#0, Tclass.M3.Element())
         ==> 
        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#0)]
           && M3.Contents.Link_q(read($Heap, f#0, M3.Element.c))
         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#0, M3.Element.c)))]);
    assume M3.UnionFind.Collect#canCall($Heap, this);
    ##d#0 := d0#0 - 1;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
    ##e#0 := next#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
    ##r#0 := $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
    ##C#0 := M3.UnionFind.Collect($Heap, this);
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume {:subsumption 0} M3.__default.GoodCMap#canCall(##C#0)
       ==> M3.__default.GoodCMap(##C#0)
         || (forall f#1: ref :: 
          { $Unbox(Map#Elements(##C#0)[$Box(f#1)]): DatatypeType } 
          $Is(f#1, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#0)[$Box(f#1)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#0)[$Box(f#1)]): DatatypeType)
             ==> Map#Domain(##C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#0)[$Box(f#1)]): DatatypeType))]);
    assume {:subsumption 0} Map#Domain(##C#0)[$Box(##e#0)];
    assume M3.UnionFind.Reaches#canCall(this, 
      d0#0 - 1, 
      next#0, 
      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
      M3.UnionFind.Collect($Heap, this));
    assume M3.UnionFind.Collect#canCall($Heap, this)
       && M3.UnionFind.Reaches#canCall(this, 
        d0#0 - 1, 
        next#0, 
        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
        M3.UnionFind.Collect($Heap, this));
    assume true;
    assume M3.UnionFind.Reaches($LS($LZ), 
      this, 
      d0#0 - 1, 
      next#0, 
      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
      M3.UnionFind.Collect($Heap, this));
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](140,7)
    assume {:subsumption 0} Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(next#0)];
    assume {:subsumption 0} (forall f#2: ref :: 
      { read($Heap, f#2, M3.Element.c) } 
      $Is(f#2, Tclass.M3.Element())
         ==> 
        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]
           && M3.Contents.Link_q(read($Heap, f#2, M3.Element.c))
         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#2, M3.Element.c)))]);
    assume M3.UnionFind.Collect#canCall($Heap, this);
    ##d#1 := d1#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#1, Tclass._System.nat(), $Heap);
    ##e#1 := next#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#1, Tclass.M3.Element(), $Heap);
    ##r#1 := $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(next#0)]): ref;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#1, Tclass.M3.Element(), $Heap);
    ##C#1 := M3.UnionFind.Collect($Heap, this);
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#1, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume {:subsumption 0} M3.__default.GoodCMap#canCall(##C#1)
       ==> M3.__default.GoodCMap(##C#1)
         || (forall f#3: ref :: 
          { $Unbox(Map#Elements(##C#1)[$Box(f#3)]): DatatypeType } 
          $Is(f#3, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#1)[$Box(f#3)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#1)[$Box(f#3)]): DatatypeType)
             ==> Map#Domain(##C#1)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#1)[$Box(f#3)]): DatatypeType))]);
    assume {:subsumption 0} Map#Domain(##C#1)[$Box(##e#1)];
    assume M3.UnionFind.Reaches#canCall(this, 
      d1#0, 
      next#0, 
      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(next#0)]): ref, 
      M3.UnionFind.Collect($Heap, this));
    assume M3.UnionFind.Collect#canCall($Heap, this)
       && M3.UnionFind.Reaches#canCall(this, 
        d1#0, 
        next#0, 
        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(next#0)]): ref, 
        M3.UnionFind.Collect($Heap, this));
    assume true;
    assume M3.UnionFind.Reaches($LS($LZ), 
      this, 
      d1#0, 
      next#0, 
      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(next#0)]): ref, 
      M3.UnionFind.Collect($Heap, this));
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](141,36)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    assume $Is(d0#0 - 1, Tclass._System.nat());
    d0##0 := d0#0 - 1;
    assume true;
    // ProcessCallStmt: CheckSubrange
    d1##0 := d1#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := next#0;
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
    assume true;
    // ProcessCallStmt: CheckSubrange
    r0##0 := $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref;
    assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(next#0)];
    assume true;
    // ProcessCallStmt: CheckSubrange
    r1##0 := $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(next#0)]): ref;
    assume true;
    assume (forall f#4: ref :: 
      { read($Heap, f#4, M3.Element.c) } 
      $Is(f#4, Tclass.M3.Element())
         ==> 
        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#4)]
           && M3.Contents.Link_q(read($Heap, f#4, M3.Element.c))
         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#4, M3.Element.c)))]);
    assume M3.UnionFind.Collect#canCall($Heap, this);
    assume M3.UnionFind.Collect#canCall($Heap, this);
    // ProcessCallStmt: CheckSubrange
    C##0 := M3.UnionFind.Collect($Heap, this);
    assume (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$M3.UnionFind.Reaches__SinkIsFunctionOfStart(this, d0##0, d1##0, e##0, r0##0, r1##0, C##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](141,79)"} true;
}



procedure {:autocontracts false} {:_induction this, d0#0, d1#0, e#0, r0#0, r1#0, C#0} CheckWellformed$$M3.UnionFind.Reaches__SinkIsFunctionOfStart(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:autocontracts false} {:_induction this, d0#0, d1#0, e#0, r0#0, r1#0, C#0} Call$$M3.UnionFind.Reaches__SinkIsFunctionOfStart(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#2: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType } 
        $Is(f#2, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#2)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d0#0, e#0, r0#0, C#0);
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d1#0, e#0, r1#0, C#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures r0#0 == r1#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, d0#0, d1#0, e#0, r0#0, r1#0, C#0} Impl$$M3.UnionFind.Reaches__SinkIsFunctionOfStart(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d0#0: int where LitInt(0) <= d0#0, 
    d1#0: int where LitInt(0) <= d1#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r0#0: ref
       where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap), 
    r1#0: ref
       where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#3: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType } 
      $Is(f#3, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#3)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d0#0, e#0, r0#0, C#0);
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d1#0, e#0, r1#0, C#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures $_reverifyPost ==> r0#0 == r1#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, d0#0, d1#0, e#0, r0#0, r1#0, C#0} Impl$$M3.UnionFind.Reaches__SinkIsFunctionOfStart(this: ref, 
    d0#0: int, 
    d1#0: int, 
    e#0: ref, 
    r0#0: ref, 
    r1#0: ref, 
    C#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Reaches_SinkIsFunctionOfStart, Impl$$M3.UnionFind.Reaches__SinkIsFunctionOfStart
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](149,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#d00#0: int, 
        $ih#d10#0: int, 
        $ih#e0#0: ref, 
        $ih#r00#0: ref, 
        $ih#r10#0: ref, 
        $ih#C0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && LitInt(0) <= $ih#d00#0
           && LitInt(0) <= $ih#d10#0
           && $Is($ih#e0#0, Tclass.M3.Element())
           && $Is($ih#r00#0, Tclass.M3.Element())
           && $Is($ih#r10#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && Map#Domain($ih#C0#0)[$Box($ih#e0#0)]
           && 
          M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#d00#0, $ih#e0#0, $ih#r00#0, $ih#C0#0)
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#d10#0, $ih#e0#0, $ih#r10#0, $ih#C0#0)
           && ((0 <= $ih#d00#0 && $ih#d00#0 < d0#0)
             || ($ih#d00#0 == d0#0
               && ((0 <= $ih#d10#0 && $ih#d10#0 < d1#0)
                 || ($ih#d10#0 == d1#0
                   && (($ih#e0#0 == null && e#0 != null)
                     || (($ih#e0#0 != null <==> e#0 != null)
                       && (($ih#r00#0 == null && r0#0 != null)
                         || (($ih#r00#0 != null <==> r0#0 != null)
                           && (($ih#r10#0 == null && r1#0 != null)
                             || (($ih#r10#0 != null <==> r1#0 != null)
                               && 
                              Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                               && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0))))))))))))
         ==> $ih#r00#0 == $ih#r10#0);
    $_reverifyPost := false;
}



procedure CheckWellformed$$M3.UnionFind.FindAux(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$M3.UnionFind.FindAux(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap));
  // user-defined preconditions
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#3: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref } 
            $Is(e#3, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#4: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)] } 
            $Is(e#4, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#5: ref :: 
            { read($Heap, e#5, M3.Element.c) } 
            $Is(e#5, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]
                 && M3.Contents.Link_q(read($Heap, e#5, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#5, M3.Element.c)))]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#6: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#6)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#6)] } 
            $Is(e#6, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#6)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#6)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#6)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#6)]): ref, 
                        M3.Element.c)), 
                    e#6, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#6)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), 
    this, 
    d#0, 
    e#0, 
    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
    M3.UnionFind.Collect($Heap, this));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  free ensures M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Map#Equal(read($Heap, this, M3.UnionFind.M), read(old($Heap), this, M3.UnionFind.M));
  ensures $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref == r#0;
  free ensures (forall d#2: int, e#2: ref, r#2: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect($Heap, this)) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this)) } 
    LitInt(0) <= d#2
         && $Is(e#2, Tclass.M3.Element())
         && $Is(r#2, Tclass.M3.Element())
       ==> M3.UnionFind.Collect#canCall(old($Heap), this)
         && (Map#Domain(M3.UnionFind.Collect(old($Heap), this))[$Box(e#2)]
           ==> M3.UnionFind.Collect#canCall(old($Heap), this)
             && M3.UnionFind.Reaches#canCall(this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this))
             && (M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this))
               ==> M3.UnionFind.Collect#canCall($Heap, this)
                 && M3.UnionFind.Reaches#canCall(this, d#2, e#2, r#2, M3.UnionFind.Collect($Heap, this)))));
  free ensures (forall d#2: int, e#2: ref, r#2: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect($Heap, this)) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this)) } 
    LitInt(0) <= d#2
         && $Is(e#2, Tclass.M3.Element())
         && $Is(r#2, Tclass.M3.Element())
       ==> 
      Map#Domain(M3.UnionFind.Collect(old($Heap), this))[$Box(e#2)]
         && M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this))
       ==> M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect($Heap, this)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$M3.UnionFind.FindAux(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap))
   returns (defass#r#0: bool, 
    r#0: ref
       where defass#r#0
         ==> $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    $_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), 
    this, 
    d#0, 
    e#0, 
    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref, 
    M3.UnionFind.Collect($Heap, this));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#15: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]): ref } 
            $Is(e#15, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#16: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)] } 
            $Is(e#16, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#17: ref :: 
            { read($Heap, e#17, M3.Element.c) } 
            $Is(e#17, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]
                 && M3.Contents.Link_q(read($Heap, e#17, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#17, M3.Element.c)))]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#18: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#18)] } 
            $Is(e#18, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]): ref, 
                        M3.Element.c)), 
                    e#18, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#18)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  free ensures true;
  ensures $_reverifyPost
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
           && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures $_reverifyPost
     ==> Map#Equal(read($Heap, this, M3.UnionFind.M), read(old($Heap), this, M3.UnionFind.M));
  ensures $_reverifyPost
     ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref == r#0;
  free ensures (forall d#2: int, e#2: ref, r#2: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect($Heap, this)) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this)) } 
    LitInt(0) <= d#2
         && $Is(e#2, Tclass.M3.Element())
         && $Is(r#2, Tclass.M3.Element())
       ==> M3.UnionFind.Collect#canCall(old($Heap), this)
         && (Map#Domain(M3.UnionFind.Collect(old($Heap), this))[$Box(e#2)]
           ==> M3.UnionFind.Collect#canCall(old($Heap), this)
             && M3.UnionFind.Reaches#canCall(this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this))
             && (M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this))
               ==> M3.UnionFind.Collect#canCall($Heap, this)
                 && M3.UnionFind.Reaches#canCall(this, d#2, e#2, r#2, M3.UnionFind.Collect($Heap, this)))));
  ensures $_reverifyPost
     ==> (forall d#2: int, e#2: ref, r#2: ref :: 
      { M3.UnionFind.Reaches($LS($LS($LZ)), this, d#2, e#2, r#2, M3.UnionFind.Collect($Heap, this)) } 
        { M3.UnionFind.Reaches($LS($LS($LZ)), this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this)) } 
      LitInt(0) <= d#2
           && $Is(e#2, Tclass.M3.Element())
           && $Is(r#2, Tclass.M3.Element())
         ==> 
        Map#Domain(M3.UnionFind.Collect(old($Heap), this))[$Box(e#2)]
           && M3.UnionFind.Reaches($LS($LS($LZ)), this, d#2, e#2, r#2, M3.UnionFind.Collect(old($Heap), this))
         ==> M3.UnionFind.Reaches($LS($LS($LZ)), this, d#2, e#2, r#2, M3.UnionFind.Collect($Heap, this)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$M3.UnionFind.FindAux(this: ref, d#0: int, e#0: ref)
   returns (defass#r#0: bool, r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#1#0_0: ref;
  var next#0_0: ref;
  var let#0_0#0#0: ref;
  var e##0_0: ref;
  var $rhs##0_0: ref
     where $Is($rhs##0_0, Tclass.M3.Element())
       && $IsAlloc($rhs##0_0, Tclass.M3.Element(), $Heap);
  var d##0_0: int;
  var e##0_1: ref;
  var C#0_0: Map Box Box
     where $Is(C#0_0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
       && $IsAlloc(C#0_0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
  var $rhs#0_0: DatatypeType where $Is($rhs#0_0, Tclass.M3.Contents());
  var td##0_0: int;
  var tt##0_0: ref;
  var tm##0_0: ref;
  var C##0_0: Map Box Box;
  var C'##0_0: Map Box Box;
  var _mcc#0#1_0: int;

    // AddMethodImpl: FindAux, Impl$$M3.UnionFind.FindAux
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, M3.UnionFind.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](156,4): initial state"} true;
    $_reverifyPost := false;
    assume e#0 != null;
    assume true;
    havoc _mcc#1#0_0;
    havoc _mcc#0#1_0;
    if (read($Heap, e#0, M3.Element.c) == #M3.Contents.Root(_mcc#0#1_0))
    {
        assume LitInt(0) <= _mcc#0#1_0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](159,11)
        assume true;
        assume true;
        r#0 := e#0;
        defass#r#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](159,14)"} true;
    }
    else if (read($Heap, e#0, M3.Element.c) == #M3.Contents.Link(_mcc#1#0_0))
    {
        assume $Is(_mcc#1#0_0, Tclass.M3.Element())
           && $IsAlloc(_mcc#1#0_0, Tclass.M3.Element(), $Heap);
        havoc next#0_0;
        assume $Is(next#0_0, Tclass.M3.Element?())
           && $IsAlloc(next#0_0, Tclass.M3.Element?(), $Heap);
        assume let#0_0#0#0 == _mcc#1#0_0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(let#0_0#0#0, Tclass.M3.Element?());
        assume next#0_0 == let#0_0#0#0;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](161,24)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##0_0 := e#0;
        assume (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.NextReachesSame(this, e##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](161,26)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](162,21)
        assume true;
        // TrCallStmt: Adding lhs with type Element
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assume $Is(d#0 - 1, Tclass._System.nat());
        d##0_0 := d#0 - 1;
        assume true;
        // ProcessCallStmt: CheckSubrange
        assume $Is(next#0_0, Tclass.M3.Element());
        e##0_1 := next#0_0;
        assume (forall<alpha> $o: ref, $f: Field alpha :: 
          $o != null
               && read($Heap, $o, alloc)
               && read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
             ==> $_Frame[$o, $f]);
        assume 0 <= d#0 || d##0_0 == d#0;
        assume d##0_0 < d#0 || (d##0_0 == d#0 && e##0_1 == null && e#0 != null);
        // ProcessCallStmt: Make the call
        call $rhs##0_0 := Call$$M3.UnionFind.FindAux(this, d##0_0, e##0_1);
        // TrCallStmt: After ProcessCallStmt
        r#0 := $rhs##0_0;
        defass#r#0 := true;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](162,31)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](163,21)
        assume true;
        assume true;
        assume (forall f#0_0: ref :: 
          { read($Heap, f#0_0, M3.Element.c) } 
          $Is(f#0_0, Tclass.M3.Element())
             ==> 
            Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#0_0)]
               && M3.Contents.Link_q(read($Heap, f#0_0, M3.Element.c))
             ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#0_0, M3.Element.c)))]);
        assume M3.UnionFind.Collect#canCall($Heap, this);
        assume M3.UnionFind.Collect#canCall($Heap, this);
        C#0_0 := M3.UnionFind.Collect($Heap, this);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](163,32)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](164,13)
        assume e#0 != null;
        assume true;
        assume $_Frame[e#0, M3.Element.c];
        assume defass#r#0;
        assume true;
        $rhs#0_0 := #M3.Contents.Link(r#0);
        $Heap := update($Heap, e#0, M3.Element.c, $rhs#0_0);
        assume $IsGoodHeap($Heap);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](164,22)"} true;
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](165,31)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        td##0_0 := d#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        tt##0_0 := e#0;
        assume defass#r#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        tm##0_0 := r#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##0_0 := C#0_0;
        assume true;
        assume (forall f#0_1: ref :: 
          { read($Heap, f#0_1, M3.Element.c) } 
          $Is(f#0_1, Tclass.M3.Element())
             ==> 
            Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#0_1)]
               && M3.Contents.Link_q(read($Heap, f#0_1, M3.Element.c))
             ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#0_1, M3.Element.c)))]);
        assume M3.UnionFind.Collect#canCall($Heap, this);
        assume M3.UnionFind.Collect#canCall($Heap, this);
        // ProcessCallStmt: CheckSubrange
        C'##0_0 := M3.UnionFind.Collect($Heap, this);
        assume (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.UpdateMaintainsReaches(this, td##0_0, tt##0_0, tm##0_0, C##0_0, C'##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](165,53)"} true;
    }
    else
    {
        assume false;
    }

    assert defass#r#0;
}



procedure {:autocontracts false} {:_induction this, td#0, tt#0, tm#0, C#0, C'#0} CheckWellformed$$M3.UnionFind.UpdateMaintainsReaches(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:autocontracts false} {:_induction this, td#0, tt#0, tm#0, C#0, C'#0} Call$$M3.UnionFind.UpdateMaintainsReaches(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#5: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType } 
        $Is(f#5, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#5)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(tt#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, td#0, tt#0, tm#0, C#0);
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(tt#0), $Box(#M3.Contents.Link(tm#0))));
  requires M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(tt#0)]): DatatypeType);
  requires Map#Domain(C'#0)[$Box(tm#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C'#0)[$Box(tm#0)]): DatatypeType);
  requires (forall f#2: ref :: 
    { $Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType } 
    $Is(f#2, Tclass.M3.Element?())
       ==> 
      Map#Domain(C#0)[$Box(f#2)]
         && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType)
       ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
       ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C#0)
         && (M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
           ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C'#0)));
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
         && M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
       ==> M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, td#0, tt#0, tm#0, C#0, C'#0} Impl$$M3.UnionFind.UpdateMaintainsReaches(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#6: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType } 
      $Is(f#6, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#6)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(tt#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, td#0, tt#0, tm#0, C#0);
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(tt#0), $Box(#M3.Contents.Link(tm#0))));
  requires M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(tt#0)]): DatatypeType);
  requires Map#Domain(C'#0)[$Box(tm#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C'#0)[$Box(tm#0)]): DatatypeType);
  requires (forall f#2: ref :: 
    { $Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType } 
    $Is(f#2, Tclass.M3.Element?())
       ==> 
      Map#Domain(C#0)[$Box(f#2)]
         && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType)
       ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures (forall d#1: int, e#1: ref, r#1: ref :: 
    { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C'#0) } 
      { M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0) } 
    LitInt(0) <= d#1
         && $Is(e#1, Tclass.M3.Element())
         && $Is(r#1, Tclass.M3.Element())
       ==> 
      Map#Domain(C#0)[$Box(e#1)]
       ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C#0)
         && (M3.UnionFind.Reaches($LS($LZ), this, d#1, e#1, r#1, C#0)
           ==> M3.UnionFind.Reaches#canCall(this, d#1, e#1, r#1, C'#0)));
  ensures $_reverifyPost
     ==> (forall d#1: int, e#1: ref, r#1: ref :: 
      { M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C'#0) } 
        { M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C#0) } 
      LitInt(0) <= d#1
           && $Is(e#1, Tclass.M3.Element())
           && $Is(r#1, Tclass.M3.Element())
         ==> 
        Map#Domain(C#0)[$Box(e#1)]
           && M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C#0)
         ==> M3.UnionFind.Reaches($LS($LS($LZ)), this, d#1, e#1, r#1, C'#0));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, td#0, tt#0, tm#0, C#0, C'#0} Impl$$M3.UnionFind.UpdateMaintainsReaches(this: ref, td#0: int, tt#0: ref, tm#0: ref, C#0: Map Box Box, C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var d#3: int;
  var e#3: ref;
  var r#3: ref;
  var ##d#3: int;
  var ##e#3: ref;
  var ##r#3: ref;
  var ##C#4: Map Box Box;
  var d##0: int;
  var e##0: ref;
  var r##0: ref;
  var C##0: Map Box Box;
  var td##0: int;
  var tt##0: ref;
  var tm##0: ref;
  var C'##0: Map Box Box;

    // AddMethodImpl: UpdateMaintainsReaches, Impl$$M3.UnionFind.UpdateMaintainsReaches
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](174,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#td0#0: int, 
        $ih#tt0#0: ref, 
        $ih#tm0#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && LitInt(0) <= $ih#td0#0
           && $Is($ih#tt0#0, Tclass.M3.Element())
           && $Is($ih#tm0#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#tt0#0)]
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#td0#0, $ih#tt0#0, $ih#tm0#0, $ih#C0#0)
           && 
          Map#Equal($ih#C'0#0, 
            Map#Build($ih#C0#0, $Box($ih#tt0#0), $Box(#M3.Contents.Link($ih#tm0#0))))
           && M3.Contents.Link_q($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#tt0#0)]): DatatypeType)
           && Map#Domain($ih#C'0#0)[$Box($ih#tm0#0)]
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#tm0#0)]): DatatypeType)
           && (forall f#7: ref :: 
            { $Unbox(Map#Elements($ih#C'0#0)[$Box(f#7)]): DatatypeType } 
            $Is(f#7, Tclass.M3.Element?())
               ==> 
              Map#Domain($ih#C0#0)[$Box(f#7)]
                 && M3.Contents.Link_q($Unbox(Map#Elements($ih#C'0#0)[$Box(f#7)]): DatatypeType)
               ==> Map#Domain($ih#C0#0)[$Box(M3.Contents.next($Unbox(Map#Elements($ih#C'0#0)[$Box(f#7)]): DatatypeType))])
           && ((0 <= $ih#td0#0 && $ih#td0#0 < td#0)
             || ($ih#td0#0 == td#0
               && (($ih#tt0#0 == null && tt#0 != null)
                 || (($ih#tt0#0 != null <==> tt#0 != null)
                   && (($ih#tm0#0 == null && tm#0 != null)
                     || (($ih#tm0#0 != null <==> tm#0 != null)
                       && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                         || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && 
                          Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                           && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))))
         ==> (forall d#2: int, e#2: ref, r#2: ref :: 
          { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, $ih#C'0#0) } 
            { M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, $ih#C0#0) } 
          LitInt(0) <= d#2
               && $Is(e#2, Tclass.M3.Element())
               && $Is(r#2, Tclass.M3.Element())
             ==> 
            Map#Domain($ih#C0#0)[$Box(e#2)]
               && M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, $ih#C0#0)
             ==> M3.UnionFind.Reaches($LS($LZ), this, d#2, e#2, r#2, $ih#C'0#0)));
    $_reverifyPost := false;
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](175,7)
    if (*)
    {
        // Assume Fuel Constant
        havoc d#3, e#3, r#3;
        assume LitInt(0) <= d#3
           && $Is(e#3, Tclass.M3.Element())
           && $Is(r#3, Tclass.M3.Element());
        if (Map#Domain(C#0)[$Box(e#3)])
        {
            ##d#3 := d#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##d#3, Tclass._System.nat(), $Heap);
            ##e#3 := e#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#3, Tclass.M3.Element(), $Heap);
            ##r#3 := r#3;
            // assume allocatedness for argument to function
            assume $IsAlloc(##r#3, Tclass.M3.Element(), $Heap);
            ##C#4 := C#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##C#4, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
            assume {:subsumption 0} M3.__default.GoodCMap#canCall(##C#4)
               ==> M3.__default.GoodCMap(##C#4)
                 || (forall f#8: ref :: 
                  { $Unbox(Map#Elements(##C#4)[$Box(f#8)]): DatatypeType } 
                  $Is(f#8, Tclass.M3.Element?())
                     ==> 
                    Map#Domain(##C#4)[$Box(f#8)]
                       && M3.Contents.Link_q($Unbox(Map#Elements(##C#4)[$Box(f#8)]): DatatypeType)
                     ==> Map#Domain(##C#4)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#4)[$Box(f#8)]): DatatypeType))]);
            assume {:subsumption 0} Map#Domain(##C#4)[$Box(##e#3)];
            assume M3.UnionFind.Reaches#canCall(this, d#3, e#3, r#3, C#0);
        }

        assume Map#Domain(C#0)[$Box(e#3)]
           ==> M3.UnionFind.Reaches#canCall(this, d#3, e#3, r#3, C#0);
        assume Map#Domain(C#0)[$Box(e#3)]
           && M3.UnionFind.Reaches($LS($LZ), this, d#3, e#3, r#3, C#0);
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](178,23)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d##0 := d#3;
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##0 := e#3;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r##0 := r#3;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##0 := C#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        td##0 := td#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        tt##0 := tt#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        tm##0 := tm#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C'##0 := C'#0;
        assume (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.ConstructReach(this, d##0, e##0, r##0, C##0, td##0, tt##0, tm##0, C'##0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](178,50)"} true;
        assume M3.UnionFind.Reaches($LS($LS($LZ)), this, d#3, e#3, r#3, C'#0);
        assume false;
    }
    else
    {
        assume (forall d#4: int, e#4: ref, r#4: ref :: 
          { M3.UnionFind.Reaches($LS($LZ), this, d#4, e#4, r#4, C'#0) } 
            { M3.UnionFind.Reaches($LS($LZ), this, d#4, e#4, r#4, C#0) } 
          LitInt(0) <= d#4
               && $Is(e#4, Tclass.M3.Element())
               && $Is(r#4, Tclass.M3.Element())
               && 
              Map#Domain(C#0)[$Box(e#4)]
               && M3.UnionFind.Reaches($LS($LZ), this, d#4, e#4, r#4, C#0)
             ==> M3.UnionFind.Reaches($LS($LZ), this, d#4, e#4, r#4, C'#0));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](179,6)"} true;
}



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, tm#0, C'#0} CheckWellformed$$M3.UnionFind.ConstructReach(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, tm#0, C'#0} Call$$M3.UnionFind.ConstructReach(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#3: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType } 
        $Is(f#3, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#3)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#3)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C#0);
  requires Map#Domain(C#0)[$Box(tt#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, td#0, tt#0, tm#0, C#0);
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(tt#0), $Box(#M3.Contents.Link(tm#0))));
  requires M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(tt#0)]): DatatypeType);
  requires Map#Domain(C'#0)[$Box(tm#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C'#0)[$Box(tm#0)]): DatatypeType);
  requires M3.__default.GoodCMap#canCall(C'#0)
     ==> M3.__default.GoodCMap(C'#0)
       || (forall f#4: ref :: 
        { $Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType } 
        $Is(f#4, Tclass.M3.Element?())
           ==> 
          Map#Domain(C'#0)[$Box(f#4)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType)
           ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#4)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, tm#0, C'#0} Impl$$M3.UnionFind.ConstructReach(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    td#0: int where LitInt(0) <= td#0, 
    tt#0: ref
       where $Is(tt#0, Tclass.M3.Element()) && $IsAlloc(tt#0, Tclass.M3.Element(), $Heap), 
    tm#0: ref
       where $Is(tm#0, Tclass.M3.Element()) && $IsAlloc(tm#0, Tclass.M3.Element(), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#5: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType } 
      $Is(f#5, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#5)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#5)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C#0);
  requires Map#Domain(C#0)[$Box(tt#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, td#0, tt#0, tm#0, C#0);
  requires Map#Equal(C'#0, Map#Build(C#0, $Box(tt#0), $Box(#M3.Contents.Link(tm#0))));
  requires M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(tt#0)]): DatatypeType);
  requires Map#Domain(C'#0)[$Box(tm#0)];
  requires M3.Contents.Root_q($Unbox(Map#Elements(C'#0)[$Box(tm#0)]): DatatypeType);
  free requires M3.__default.GoodCMap#canCall(C'#0)
     && 
    M3.__default.GoodCMap(C'#0)
     && (forall f#6: ref :: 
      { $Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType } 
      $Is(f#6, Tclass.M3.Element?())
         ==> 
        Map#Domain(C'#0)[$Box(f#6)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType)
         ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#6)]): DatatypeType))]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
  ensures $_reverifyPost
     ==> M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, td#0, tt#0, tm#0, C'#0} Impl$$M3.UnionFind.ConstructReach(this: ref, 
    d#0: int, 
    e#0: ref, 
    r#0: ref, 
    C#0: Map Box Box, 
    td#0: int, 
    tt#0: ref, 
    tm#0: ref, 
    C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var d0##0_0: int;
  var d1##0_0: int;
  var e##0_0: ref;
  var r0##0_0: ref;
  var r1##0_0: ref;
  var C##0_0: Map Box Box;
  var _mcc#1#1_0: ref;
  var next#1_0: ref;
  var let#1_0#0#0: ref;
  var d##1_0: int;
  var e##1_0: ref;
  var r##1_0: ref;
  var C##1_0: Map Box Box;
  var td##1_0: int;
  var tt##1_0: ref;
  var tm##1_0: ref;
  var C'##1_0: Map Box Box;
  var _mcc#0#2_0: int;

    // AddMethodImpl: ConstructReach, Impl$$M3.UnionFind.ConstructReach
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](190,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#d0#0: int, 
        $ih#e0#0: ref, 
        $ih#r0#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#td0#0: int, 
        $ih#tt0#0: ref, 
        $ih#tm0#0: ref, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && LitInt(0) <= $ih#d0#0
           && $Is($ih#e0#0, Tclass.M3.Element())
           && $Is($ih#r0#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && LitInt(0) <= $ih#td0#0
           && $Is($ih#tt0#0, Tclass.M3.Element())
           && $Is($ih#tm0#0, Tclass.M3.Element())
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && Map#Domain($ih#C0#0)[$Box($ih#e0#0)]
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#d0#0, $ih#e0#0, $ih#r0#0, $ih#C0#0)
           && 
          Map#Domain($ih#C0#0)[$Box($ih#tt0#0)]
           && M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#td0#0, $ih#tt0#0, $ih#tm0#0, $ih#C0#0)
           && 
          Map#Equal($ih#C'0#0, 
            Map#Build($ih#C0#0, $Box($ih#tt0#0), $Box(#M3.Contents.Link($ih#tm0#0))))
           && M3.Contents.Link_q($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#tt0#0)]): DatatypeType)
           && Map#Domain($ih#C'0#0)[$Box($ih#tm0#0)]
           && M3.Contents.Root_q($Unbox(Map#Elements($ih#C'0#0)[$Box($ih#tm0#0)]): DatatypeType)
           && M3.__default.GoodCMap($ih#C'0#0)
           && ((0 <= $ih#d0#0 && $ih#d0#0 < d#0)
             || ($ih#d0#0 == d#0
               && (($ih#e0#0 == null && e#0 != null)
                 || (($ih#e0#0 != null <==> e#0 != null)
                   && (($ih#r0#0 == null && r#0 != null)
                     || (($ih#r0#0 != null <==> r#0 != null)
                       && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                         || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && ((0 <= $ih#td0#0 && $ih#td0#0 < td#0)
                             || ($ih#td0#0 == td#0
                               && (($ih#tt0#0 == null && tt#0 != null)
                                 || (($ih#tt0#0 != null <==> tt#0 != null)
                                   && (($ih#tm0#0 == null && tm#0 != null)
                                     || (($ih#tm0#0 != null <==> tm#0 != null)
                                       && 
                                      Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                                       && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))))))))))
         ==> M3.UnionFind.Reaches($LS($LZ), this, $ih#d0#0, $ih#e0#0, $ih#r0#0, $ih#C'0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](191,7)
    assume true;
    if (e#0 == tt#0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](192,38)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d0##0_0 := d#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        d1##0_0 := td#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        e##0_0 := e#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r0##0_0 := r#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        r1##0_0 := tm#0;
        assume true;
        // ProcessCallStmt: CheckSubrange
        C##0_0 := C#0;
        assume (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$M3.UnionFind.Reaches__SinkIsFunctionOfStart(this, d0##0_0, d1##0_0, e##0_0, r0##0_0, r1##0_0, C##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](192,57)"} true;
    }
    else
    {
        assume Map#Domain(C#0)[$Box(e#0)];
        assume true;
        havoc _mcc#1#1_0;
        havoc _mcc#0#2_0;
        if ($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType
           == #M3.Contents.Root(_mcc#0#2_0))
        {
            assume LitInt(0) <= _mcc#0#2_0;
        }
        else if ($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType
           == #M3.Contents.Link(_mcc#1#1_0))
        {
            assume $Is(_mcc#1#1_0, Tclass.M3.Element());
            havoc next#1_0;
            assume $Is(next#1_0, Tclass.M3.Element?())
               && $IsAlloc(next#1_0, Tclass.M3.Element?(), $Heap);
            assume let#1_0#0#0 == _mcc#1#1_0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1_0#0#0, Tclass.M3.Element?());
            assume next#1_0 == let#1_0#0#0;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](197,25)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assume $Is(d#0 - 1, Tclass._System.nat());
            d##1_0 := d#0 - 1;
            assume true;
            // ProcessCallStmt: CheckSubrange
            assume $Is(next#1_0, Tclass.M3.Element());
            e##1_0 := next#1_0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            r##1_0 := r#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            C##1_0 := C#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            td##1_0 := td#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            tt##1_0 := tt#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            tm##1_0 := tm#0;
            assume true;
            // ProcessCallStmt: CheckSubrange
            C'##1_0 := C'#0;
            assume (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume 0 <= d#0 || d##1_0 == d#0;
            assume 0 <= td#0
               || d##1_0 < d#0
               || (e##1_0 == null && e#0 != null)
               || (r##1_0 == null && r#0 != null)
               || (Set#Subset(Map#Domain(C##1_0), Map#Domain(C#0))
                 && !Set#Subset(Map#Domain(C#0), Map#Domain(C##1_0)))
               || td##1_0 == td#0;
            assume d##1_0 < d#0
               || (d##1_0 == d#0
                 && ((e##1_0 == null && e#0 != null)
                   || ((e##1_0 != null <==> e#0 != null)
                     && ((r##1_0 == null && r#0 != null)
                       || ((r##1_0 != null <==> r#0 != null)
                         && ((Set#Subset(Map#Domain(C##1_0), Map#Domain(C#0))
                             && !Set#Subset(Map#Domain(C#0), Map#Domain(C##1_0)))
                           || (Set#Equal(Map#Domain(C##1_0), Map#Domain(C#0))
                             && (td##1_0 < td#0
                               || (td##1_0 == td#0
                                 && ((tt##1_0 == null && tt#0 != null)
                                   || ((tt##1_0 != null <==> tt#0 != null)
                                     && ((tm##1_0 == null && tm#0 != null)
                                       || ((tm##1_0 != null <==> tm#0 != null)
                                         && 
                                        Set#Subset(Map#Domain(C'##1_0), Map#Domain(C'#0))
                                         && !Set#Subset(Map#Domain(C'#0), Map#Domain(C'##1_0)))))))))))))));
            // ProcessCallStmt: Make the call
            call Call$$M3.UnionFind.ConstructReach(this, d##1_0, e##1_0, r##1_0, C##1_0, td##1_0, tt##1_0, tm##1_0, C'##1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M3](197,57)"} true;
        }
        else
        {
            assume false;
        }
    }
}



// function declaration for M3.UnionFind.ValidM1
function M3.UnionFind.ValidM1($heap: Heap, this: ref) : bool;

function M3.UnionFind.ValidM1#canCall($heap: Heap, this: ref) : bool;

// frame axiom for M3.UnionFind.ValidM1
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), M3.UnionFind.ValidM1($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.M3.UnionFind())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, M3.UnionFind.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> M3.UnionFind.ValidM1($h0, this) == M3.UnionFind.ValidM1($h1, this));

// consequence axiom for M3.UnionFind.ValidM1
axiom 7 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { M3.UnionFind.ValidM1($Heap, this) } 
    M3.UnionFind.ValidM1#canCall($Heap, this)
         || (7 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap))
       ==> 
      Map#Equal(read($Heap, this, M3.UnionFind.M), Map#Empty(): Map Box Box)
       ==> M3.UnionFind.ValidM1($Heap, this));

function M3.UnionFind.ValidM1#requires(Heap, ref) : bool;

// #requires axiom for M3.UnionFind.ValidM1
axiom (forall $Heap: Heap, this: ref :: 
  { M3.UnionFind.ValidM1#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.M3.UnionFind())
       && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
     ==> M3.UnionFind.ValidM1#requires($Heap, this) == true);

// definition axiom for M3.UnionFind.ValidM1 (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { M3.UnionFind.ValidM1($Heap, this), $IsGoodHeap($Heap) } 
    M3.UnionFind.ValidM1#canCall($Heap, this)
         || (7 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap))
       ==> (Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr))
           ==> 
          (forall e#0: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref } 
            $Is(e#0, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]])
           ==> 
          (forall e#1: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1)] } 
            $Is(e#1, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]): ref)
           ==> 
          (forall e#2: ref :: 
            { read($Heap, e#2, M3.Element.c) } 
            $Is(e#2, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]
                 && M3.Contents.Link_q(read($Heap, e#2, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#2, M3.Element.c)))])
           ==> (forall e#3: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)] } 
            $Is(e#3, Tclass.M3.Element())
               ==> 
              (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
               ==> M3.Contents.Root_q(read($Heap, 
                  $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref, 
                  M3.Element.c)))
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
               ==> M3.UnionFind.Collect#canCall($Heap, this)
                 && M3.UnionFind.Reaches#canCall(this, 
                  M3.Contents.depth(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref, 
                      M3.Element.c)), 
                  e#3, 
                  $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref, 
                  M3.UnionFind.Collect($Heap, this))))
         && M3.UnionFind.ValidM1($Heap, this)
           == (
            Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
              read($Heap, this, M3.UnionFind.Repr))
             && 
            (forall e#0: ref :: 
              { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]): ref } 
              $Is(e#0, Tclass.M3.Element?())
                 ==> 
                Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]
                 ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#0)]])
             && (forall e#1: ref :: 
              { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]]): ref } 
                { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1)] } 
              $Is(e#1, Tclass.M3.Element?())
                 ==> 
                Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]
                 ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]]): ref
                   == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]): ref)
             && (forall e#2: ref :: 
              { read($Heap, e#2, M3.Element.c) } 
              $Is(e#2, Tclass.M3.Element())
                 ==> 
                Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]
                   && M3.Contents.Link_q(read($Heap, e#2, M3.Element.c))
                 ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#2, M3.Element.c)))])
             && (forall e#3: ref :: 
              { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref } 
                { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)] } 
              $Is(e#3, Tclass.M3.Element())
                 ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
                     ==> M3.Contents.Root_q(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref, 
                        M3.Element.c)))
                   && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
                     ==> M3.UnionFind.Reaches($LS($LZ), 
                      this, 
                      M3.Contents.depth(read($Heap, 
                          $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref, 
                          M3.Element.c)), 
                      e#3, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref, 
                      M3.UnionFind.Collect($Heap, this))))));

procedure {:autocontracts false} CheckWellformed$$M3.UnionFind.ValidM1(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for M3.UnionFind.Collect
function M3.UnionFind.Collect($heap: Heap, this: ref) : Map Box Box;

function M3.UnionFind.Collect#canCall($heap: Heap, this: ref) : bool;

// frame axiom for M3.UnionFind.Collect
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), M3.UnionFind.Collect($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.M3.UnionFind())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && ($o == this
             || ($Is($o, Tclass.M3.Element())
               && Map#Domain(read($h0, this, M3.UnionFind.M))[$Box($o)]))
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> M3.UnionFind.Collect($h0, this) == M3.UnionFind.Collect($h1, this));

// consequence axiom for M3.UnionFind.Collect
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { M3.UnionFind.Collect($Heap, this) } 
    M3.UnionFind.Collect#canCall($Heap, this)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
           && (forall f#0: ref :: 
            { read($Heap, f#0, M3.Element.c) } 
            $Is(f#0, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#0)]
                 && M3.Contents.Link_q(read($Heap, f#0, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#0, M3.Element.c)))]))
       ==> M3.__default.GoodCMap(M3.UnionFind.Collect($Heap, this))
         && $Is(M3.UnionFind.Collect($Heap, this), 
          TMap(Tclass.M3.Element(), Tclass.M3.Contents())));

function M3.UnionFind.Collect#requires(Heap, ref) : bool;

// #requires axiom for M3.UnionFind.Collect
axiom (forall $Heap: Heap, this: ref :: 
  { M3.UnionFind.Collect#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.M3.UnionFind())
       && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
     ==> M3.UnionFind.Collect#requires($Heap, this)
       == (forall f#1: ref :: 
        { read($Heap, f#1, M3.Element.c) } 
        $Is(f#1, Tclass.M3.Element())
           ==> 
          Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#1)]
             && M3.Contents.Link_q(read($Heap, f#1, M3.Element.c))
           ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#1, M3.Element.c)))]));

// definition axiom for M3.UnionFind.Collect (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { M3.UnionFind.Collect($Heap, this), $IsGoodHeap($Heap) } 
    M3.UnionFind.Collect#canCall($Heap, this)
         || (6 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
           && (forall f#1: ref :: 
            { read($Heap, f#1, M3.Element.c) } 
            $Is(f#1, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#1)]
                 && M3.Contents.Link_q(read($Heap, f#1, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#1, M3.Element.c)))]))
       ==> M3.UnionFind.Collect($Heap, this)
         == Map#Glue((lambda $w#0: Box :: 
            $Is($Unbox($w#0): ref, Tclass.M3.Element())
               && Map#Domain(read($Heap, this, M3.UnionFind.M))[$w#0]), 
          (lambda $w#0: Box :: $Box(read($Heap, $Unbox($w#0): ref, M3.Element.c))), 
          TMap(Tclass.M3.Element(), Tclass.M3.Contents())));

procedure {:autocontracts false} CheckWellformed$$M3.UnionFind.Collect(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for M3.UnionFind.Reaches
function M3.UnionFind.Reaches($ly: LayerType, this: ref, d#0: int, e#0: ref, r#0: ref, C#0: Map Box Box)
   : bool;

function M3.UnionFind.Reaches#canCall(this: ref, d#0: int, e#0: ref, r#0: ref, C#0: Map Box Box) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: ref, d#0: int, e#0: ref, r#0: ref, C#0: Map Box Box :: 
  { M3.UnionFind.Reaches($LS($ly), this, d#0, e#0, r#0, C#0) } 
  M3.UnionFind.Reaches($LS($ly), this, d#0, e#0, r#0, C#0)
     == M3.UnionFind.Reaches($ly, this, d#0, e#0, r#0, C#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: ref, d#0: int, e#0: ref, r#0: ref, C#0: Map Box Box :: 
  { M3.UnionFind.Reaches(AsFuelBottom($ly), this, d#0, e#0, r#0, C#0) } 
  M3.UnionFind.Reaches($ly, this, d#0, e#0, r#0, C#0)
     == M3.UnionFind.Reaches($LZ, this, d#0, e#0, r#0, C#0));

// consequence axiom for M3.UnionFind.Reaches
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, this: ref, d#0: int, e#0: ref, r#0: ref, C#0: Map Box Box :: 
    { M3.UnionFind.Reaches($ly, this, d#0, e#0, r#0, C#0) } 
    M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C#0)
         || (5 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass.M3.UnionFind())
           && LitInt(0) <= d#0
           && $Is(e#0, Tclass.M3.Element())
           && $Is(r#0, Tclass.M3.Element())
           && $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap(C#0)
           && Map#Domain(C#0)[$Box(e#0)])
       ==> true);

function M3.UnionFind.Reaches#requires(LayerType, ref, int, ref, ref, Map Box Box) : bool;

// #requires axiom for M3.UnionFind.Reaches
axiom (forall $ly: LayerType, 
    $Heap: Heap, 
    this: ref, 
    d#0: int, 
    e#0: ref, 
    r#0: ref, 
    C#0: Map Box Box :: 
  { M3.UnionFind.Reaches#requires($ly, this, d#0, e#0, r#0, C#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.M3.UnionFind())
       && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
       && LitInt(0) <= d#0
       && $Is(e#0, Tclass.M3.Element())
       && $Is(r#0, Tclass.M3.Element())
       && $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
     ==> M3.UnionFind.Reaches#requires($ly, this, d#0, e#0, r#0, C#0)
       == (M3.__default.GoodCMap(C#0) && Map#Domain(C#0)[$Box(e#0)]));

// definition axiom for M3.UnionFind.Reaches (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      $Heap: Heap, 
      this: ref, 
      d#0: int, 
      e#0: ref, 
      r#0: ref, 
      C#0: Map Box Box :: 
    { M3.UnionFind.Reaches($LS($ly), this, d#0, e#0, r#0, C#0), $IsGoodHeap($Heap) } 
    M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C#0)
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
           && LitInt(0) <= d#0
           && $Is(e#0, Tclass.M3.Element())
           && $Is(r#0, Tclass.M3.Element())
           && $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap(C#0)
           && Map#Domain(C#0)[$Box(e#0)])
       ==> (!M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType)
           ==> (var next#1 := M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType); 
            d#0 != 0 ==> M3.UnionFind.Reaches#canCall(this, d#0 - 1, next#1, r#0, C#0)))
         && M3.UnionFind.Reaches($LS($ly), this, d#0, e#0, r#0, C#0)
           == (if M3.Contents.Root_q($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType)
             then e#0 == r#0
             else (var next#0 := M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(e#0)]): DatatypeType); 
              d#0 != 0 && M3.UnionFind.Reaches($ly, this, d#0 - 1, next#0, r#0, C#0))));

// definition axiom for M3.UnionFind.Reaches for decreasing-related literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      $Heap: Heap, 
      this: ref, 
      d#0: int, 
      e#0: ref, 
      r#0: ref, 
      C#0: Map Box Box :: 
    {:weight 3} { M3.UnionFind.Reaches($LS($ly), this, LitInt(d#0), Lit(e#0), Lit(r#0), Lit(C#0)), $IsGoodHeap($Heap) } 
    M3.UnionFind.Reaches#canCall(this, LitInt(d#0), Lit(e#0), Lit(r#0), Lit(C#0))
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
           && LitInt(0) <= d#0
           && $Is(e#0, Tclass.M3.Element())
           && $Is(r#0, Tclass.M3.Element())
           && $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          Lit(M3.__default.GoodCMap(Lit(C#0)))
           && Map#Domain(C#0)[$Box(e#0)])
       ==> (!M3.Contents.Root_q($Unbox(Map#Elements(Lit(C#0))[$Box(Lit(e#0))]): DatatypeType)
           ==> (var next#3 := M3.Contents.next($Unbox(Map#Elements(Lit(C#0))[$Box(Lit(e#0))]): DatatypeType); 
            Lit(d#0 != 0)
               ==> M3.UnionFind.Reaches#canCall(this, LitInt(d#0 - 1), next#3, Lit(r#0), Lit(C#0))))
         && M3.UnionFind.Reaches($LS($ly), this, LitInt(d#0), Lit(e#0), Lit(r#0), Lit(C#0))
           == (if M3.Contents.Root_q($Unbox(Map#Elements(Lit(C#0))[$Box(Lit(e#0))]): DatatypeType)
             then Lit(e#0) == Lit(r#0)
             else (var next#2 := M3.Contents.next($Unbox(Map#Elements(Lit(C#0))[$Box(Lit(e#0))]): DatatypeType); 
              d#0 != 0
                 && M3.UnionFind.Reaches($LS($ly), this, LitInt(d#0 - 1), next#2, Lit(r#0), Lit(C#0)))));

// definition axiom for M3.UnionFind.Reaches for all literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, 
      $Heap: Heap, 
      this: ref, 
      d#0: int, 
      e#0: ref, 
      r#0: ref, 
      C#0: Map Box Box :: 
    {:weight 3} { M3.UnionFind.Reaches($LS($ly), Lit(this), LitInt(d#0), Lit(e#0), Lit(r#0), Lit(C#0)), $IsGoodHeap($Heap) } 
    M3.UnionFind.Reaches#canCall(Lit(this), LitInt(d#0), Lit(e#0), Lit(r#0), Lit(C#0))
         || (5 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
           && LitInt(0) <= d#0
           && $Is(e#0, Tclass.M3.Element())
           && $Is(r#0, Tclass.M3.Element())
           && $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          Lit(M3.__default.GoodCMap(Lit(C#0)))
           && Map#Domain(C#0)[$Box(e#0)])
       ==> (!M3.Contents.Root_q($Unbox(Map#Elements(Lit(C#0))[$Box(Lit(e#0))]): DatatypeType)
           ==> (var next#5 := M3.Contents.next($Unbox(Map#Elements(Lit(C#0))[$Box(Lit(e#0))]): DatatypeType); 
            Lit(d#0 != 0)
               ==> M3.UnionFind.Reaches#canCall(Lit(this), LitInt(d#0 - 1), next#5, Lit(r#0), Lit(C#0))))
         && M3.UnionFind.Reaches($LS($ly), Lit(this), LitInt(d#0), Lit(e#0), Lit(r#0), Lit(C#0))
           == (if M3.Contents.Root_q($Unbox(Map#Elements(Lit(C#0))[$Box(Lit(e#0))]): DatatypeType)
             then Lit(e#0) == Lit(r#0)
             else (var next#4 := M3.Contents.next($Unbox(Map#Elements(Lit(C#0))[$Box(Lit(e#0))]): DatatypeType); 
              d#0 != 0
                 && M3.UnionFind.Reaches($LS($ly), Lit(this), LitInt(d#0 - 1), next#4, Lit(r#0), Lit(C#0)))));

procedure {:autocontracts false} CheckWellformed$$M3.UnionFind.Reaches(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref where $Is(e#0, Tclass.M3.Element()), 
    r#0: ref where $Is(r#0, Tclass.M3.Element()), 
    C#0: Map Box Box where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents())));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, C'#0} CheckWellformed$$M3.UnionFind.Reaches__Monotonic(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, C'#0} Call$$M3.UnionFind.Reaches__Monotonic(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap));
  // user-defined preconditions
  requires M3.__default.GoodCMap#canCall(C#0)
     ==> M3.__default.GoodCMap(C#0)
       || (forall f#4: ref :: 
        { $Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType } 
        $Is(f#4, Tclass.M3.Element?())
           ==> 
          Map#Domain(C#0)[$Box(f#4)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType)
           ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#4)]): DatatypeType))]);
  requires M3.__default.GoodCMap#canCall(C'#0)
     ==> M3.__default.GoodCMap(C'#0)
       || (forall f#5: ref :: 
        { $Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType } 
        $Is(f#5, Tclass.M3.Element?())
           ==> 
          Map#Domain(C'#0)[$Box(f#5)]
             && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType)
           ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#5)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C#0);
  requires (forall f#2: ref :: 
    { $Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType } 
      { $Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType } 
      { Map#Domain(C'#0)[$Box(f#2)] } 
      { Map#Domain(C#0)[$Box(f#2)] } 
    $Is(f#2, Tclass.M3.Element?())
       ==> (Map#Domain(C#0)[$Box(f#2)] ==> Map#Domain(C'#0)[$Box(f#2)])
         && (Map#Domain(C#0)[$Box(f#2)]
           ==> M3.Contents#Equal($Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType, 
            $Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
  ensures M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, C'#0} Impl$$M3.UnionFind.Reaches__Monotonic(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    d#0: int where LitInt(0) <= d#0, 
    e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    C#0: Map Box Box
       where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap), 
    C'#0: Map Box Box
       where $Is(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
         && $IsAlloc(C'#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap))
   returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.__default.GoodCMap#canCall(C#0)
     && 
    M3.__default.GoodCMap(C#0)
     && (forall f#6: ref :: 
      { $Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType } 
      $Is(f#6, Tclass.M3.Element?())
         ==> 
        Map#Domain(C#0)[$Box(f#6)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType)
         ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#6)]): DatatypeType))]);
  free requires M3.__default.GoodCMap#canCall(C'#0)
     && 
    M3.__default.GoodCMap(C'#0)
     && (forall f#7: ref :: 
      { $Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType } 
      $Is(f#7, Tclass.M3.Element?())
         ==> 
        Map#Domain(C'#0)[$Box(f#7)]
           && M3.Contents.Link_q($Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType)
         ==> Map#Domain(C'#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C'#0)[$Box(f#7)]): DatatypeType))]);
  requires Map#Domain(C#0)[$Box(e#0)];
  requires M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C#0);
  requires (forall f#2: ref :: 
    { $Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType } 
      { $Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType } 
      { Map#Domain(C'#0)[$Box(f#2)] } 
      { Map#Domain(C#0)[$Box(f#2)] } 
    $Is(f#2, Tclass.M3.Element?())
       ==> (Map#Domain(C#0)[$Box(f#2)] ==> Map#Domain(C'#0)[$Box(f#2)])
         && (Map#Domain(C#0)[$Box(f#2)]
           ==> M3.Contents#Equal($Unbox(Map#Elements(C#0)[$Box(f#2)]): DatatypeType, 
            $Unbox(Map#Elements(C'#0)[$Box(f#2)]): DatatypeType)));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Reaches#canCall(this, d#0, e#0, r#0, C'#0);
  ensures $_reverifyPost
     ==> M3.UnionFind.Reaches($LS($LS($LZ)), this, d#0, e#0, r#0, C'#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:autocontracts false} {:_induction this, d#0, e#0, r#0, C#0, C'#0} Impl$$M3.UnionFind.Reaches__Monotonic(this: ref, d#0: int, e#0: ref, r#0: ref, C#0: Map Box Box, C'#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Reaches_Monotonic, Impl$$M3.UnionFind.Reaches__Monotonic
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](84,4): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#this0#0: ref, 
        $ih#d0#0: int, 
        $ih#e0#0: ref, 
        $ih#r0#0: ref, 
        $ih#C0#0: Map Box Box, 
        $ih#C'0#0: Map Box Box :: 
      $Is($ih#this0#0, Tclass.M3.UnionFind())
           && LitInt(0) <= $ih#d0#0
           && $Is($ih#e0#0, Tclass.M3.Element())
           && $Is($ih#r0#0, Tclass.M3.Element())
           && $Is($ih#C0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && $Is($ih#C'0#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
           && 
          M3.__default.GoodCMap($ih#C0#0)
           && M3.__default.GoodCMap($ih#C'0#0)
           && Map#Domain($ih#C0#0)[$Box($ih#e0#0)]
           && 
          M3.UnionFind.Reaches($LS($LZ), $ih#this0#0, $ih#d0#0, $ih#e0#0, $ih#r0#0, $ih#C0#0)
           && (forall f#8: ref :: 
            { $Unbox(Map#Elements($ih#C'0#0)[$Box(f#8)]): DatatypeType } 
              { $Unbox(Map#Elements($ih#C0#0)[$Box(f#8)]): DatatypeType } 
              { Map#Domain($ih#C'0#0)[$Box(f#8)] } 
              { Map#Domain($ih#C0#0)[$Box(f#8)] } 
            $Is(f#8, Tclass.M3.Element?())
               ==> (Map#Domain($ih#C0#0)[$Box(f#8)] ==> Map#Domain($ih#C'0#0)[$Box(f#8)])
                 && (Map#Domain($ih#C0#0)[$Box(f#8)]
                   ==> M3.Contents#Equal($Unbox(Map#Elements($ih#C0#0)[$Box(f#8)]): DatatypeType, 
                    $Unbox(Map#Elements($ih#C'0#0)[$Box(f#8)]): DatatypeType)))
           && ((0 <= $ih#d0#0 && $ih#d0#0 < d#0)
             || ($ih#d0#0 == d#0
               && (($ih#e0#0 == null && e#0 != null)
                 || (($ih#e0#0 != null <==> e#0 != null)
                   && (($ih#r0#0 == null && r#0 != null)
                     || (($ih#r0#0 != null <==> r#0 != null)
                       && ((Set#Subset(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && !Set#Subset(Map#Domain(C#0), Map#Domain($ih#C0#0)))
                         || (Set#Equal(Map#Domain($ih#C0#0), Map#Domain(C#0))
                           && 
                          Set#Subset(Map#Domain($ih#C'0#0), Map#Domain(C'#0))
                           && !Set#Subset(Map#Domain(C'#0), Map#Domain($ih#C'0#0))))))))))
         ==> M3.UnionFind.Reaches($LS($LZ), this, $ih#d0#0, $ih#e0#0, $ih#r0#0, $ih#C'0#0));
    $_reverifyPost := false;
}



procedure CheckWellformed$$M3.UnionFind.New(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap))
   returns (e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$M3.UnionFind.New(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap))
   returns (e#0: ref
       where $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap));
  // user-defined preconditions
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#1: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]): ref } 
            $Is(e#1, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#1)]]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#2: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)] } 
            $Is(e#2, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]): ref));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#3: ref :: 
            { read($Heap, e#3, M3.Element.c) } 
            $Is(e#3, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
                 && M3.Contents.Link_q(read($Heap, e#3, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#3, M3.Element.c)))]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#4: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)] } 
            $Is(e#4, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                        M3.Element.c)), 
                    e#4, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  free ensures M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)];
  ensures (forall e'#1: ref :: 
    { $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e'#1)]): ref } 
      { Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e'#1)] } 
    $Is(e'#1, Tclass.M3.Element?())
       ==> 
      Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e'#1)]
       ==> $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e'#1)]): ref
         != e#0);
  free ensures true;
  ensures Map#Equal(read($Heap, this, M3.UnionFind.M), 
    Map#Build(read(old($Heap), this, M3.UnionFind.M), $Box(e#0), $Box(e#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$M3.UnionFind.New(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap))
   returns (defass#e#0: bool, 
    e#0: ref
       where defass#e#0
         ==> $Is(e#0, Tclass.M3.Element()) && $IsAlloc(e#0, Tclass.M3.Element(), $Heap), 
    $_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#13: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#13)]): ref } 
            $Is(e#13, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#13)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#13)]]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#14: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#14)] } 
            $Is(e#14, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]): ref));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#15: ref :: 
            { read($Heap, e#15, M3.Element.c) } 
            $Is(e#15, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]
                 && M3.Contents.Link_q(read($Heap, e#15, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#15, M3.Element.c)))]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#16: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)] } 
            $Is(e#16, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref, 
                        M3.Element.c)), 
                    e#16, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  free ensures true;
  ensures $_reverifyPost
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
           && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures $_reverifyPost
     ==> !Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e#0)];
  ensures $_reverifyPost
     ==> (forall e'#1: ref :: 
      { $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e'#1)]): ref } 
        { Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e'#1)] } 
      $Is(e'#1, Tclass.M3.Element?())
         ==> 
        Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(e'#1)]
         ==> $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e'#1)]): ref
           != e#0);
  free ensures true;
  ensures $_reverifyPost
     ==> Map#Equal(read($Heap, this, M3.UnionFind.M), 
      Map#Build(read(old($Heap), this, M3.UnionFind.M), $Box(e#0), $Box(e#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$M3.UnionFind.New(this: ref) returns (defass#e#0: bool, e#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $nw: ref;
  var $rhs#0: DatatypeType where $Is($rhs#0, Tclass.M3.Contents());
  var $rhs#1: Set Box where $Is($rhs#1, TSet(Tclass._System.object?()));
  var $rhs#2: Map Box Box
     where $Is($rhs#2, TMap(Tclass.M3.Element(), Tclass.M3.Element()));
  var ##d#0: int;
  var ##e#0: ref;
  var ##r#0: ref;
  var ##C#0: Map Box Box;
  var f#2: ref;
  var d##0_0: int;
  var e##0_0: ref;
  var r##0_0: ref;
  var C##0_0: Map Box Box;
  var C'##0_0: Map Box Box;

    // AddMethodImpl: New, Impl$$M3.UnionFind.New
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, M3.UnionFind.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](88,4): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](89,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass.M3.Element?();
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    e#0 := $nw;
    defass#e#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](89,22)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](90,11)
    assume defass#e#0;
    assume e#0 != null;
    assume true;
    assume $_Frame[e#0, M3.Element.c];
    assume $Is(LitInt(0), Tclass._System.nat());
    assume true;
    $rhs#0 := Lit(#M3.Contents.Root(LitInt(0)));
    $Heap := update($Heap, e#0, M3.Element.c, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](90,20)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](91,12)
    assume true;
    assume $_Frame[this, M3.UnionFind.Repr];
    assume defass#e#0;
    assume true;
    $rhs#1 := Set#Union(read($Heap, this, M3.UnionFind.Repr), 
      Set#UnionOne(Set#Empty(): Set Box, $Box(e#0)));
    $Heap := update($Heap, this, M3.UnionFind.Repr, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](91,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](92,9)
    assume true;
    assume $_Frame[this, M3.UnionFind.M];
    assume defass#e#0;
    assume defass#e#0;
    assume true;
    $rhs#2 := Map#Build(read($Heap, this, M3.UnionFind.M), $Box(e#0), $Box(e#0));
    $Heap := update($Heap, this, M3.UnionFind.M, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](92,20)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](93,7)
    assume defass#e#0;
    assume defass#e#0;
    assume {:subsumption 0} (forall f#0: ref :: 
      { read($Heap, f#0, M3.Element.c) } 
      $Is(f#0, Tclass.M3.Element())
         ==> 
        Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#0)]
           && M3.Contents.Link_q(read($Heap, f#0, M3.Element.c))
         ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#0, M3.Element.c)))]);
    assume M3.UnionFind.Collect#canCall($Heap, this);
    assume $Is(LitInt(0), Tclass._System.nat());
    ##d#0 := LitInt(0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##d#0, Tclass._System.nat(), $Heap);
    ##e#0 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass.M3.Element(), $Heap);
    ##r#0 := e#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##r#0, Tclass.M3.Element(), $Heap);
    ##C#0 := M3.UnionFind.Collect($Heap, this);
    // assume allocatedness for argument to function
    assume $IsAlloc(##C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()), $Heap);
    assume {:subsumption 0} M3.__default.GoodCMap#canCall(##C#0)
       ==> M3.__default.GoodCMap(##C#0)
         || (forall f#1: ref :: 
          { $Unbox(Map#Elements(##C#0)[$Box(f#1)]): DatatypeType } 
          $Is(f#1, Tclass.M3.Element?())
             ==> 
            Map#Domain(##C#0)[$Box(f#1)]
               && M3.Contents.Link_q($Unbox(Map#Elements(##C#0)[$Box(f#1)]): DatatypeType)
             ==> Map#Domain(##C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(##C#0)[$Box(f#1)]): DatatypeType))]);
    assume {:subsumption 0} Map#Domain(##C#0)[$Box(##e#0)];
    assume M3.UnionFind.Reaches#canCall(this, LitInt(0), e#0, e#0, M3.UnionFind.Collect($Heap, this));
    assume M3.UnionFind.Collect#canCall($Heap, this)
       && M3.UnionFind.Reaches#canCall(this, LitInt(0), e#0, e#0, M3.UnionFind.Collect($Heap, this));
    assume true;
    assume M3.UnionFind.Reaches($LS($LZ), this, LitInt(0), e#0, e#0, M3.UnionFind.Collect($Heap, this));
    // ----- forall statement (proof) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](94,7)
    if (*)
    {
        // Assume Fuel Constant
        havoc f#2;
        assume $Is(f#2, Tclass.M3.Element());
        assume true;
        assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2)];
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](97,9)
        assume defass#e#0;
        assume true;
        if (f#2 != e#0)
        {
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](98,28)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2)];
            assume $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]): ref != null;
            assume M3.Contents.Root_q(read($Heap, 
                $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]): ref, 
                M3.Element.c));
            assume true;
            // ProcessCallStmt: CheckSubrange
            d##0_0 := M3.Contents.depth(read($Heap, 
                $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]): ref, 
                M3.Element.c));
            assume true;
            // ProcessCallStmt: CheckSubrange
            e##0_0 := f#2;
            assume Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#2)];
            assume true;
            // ProcessCallStmt: CheckSubrange
            r##0_0 := $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]): ref;
            assume $IsAlloc(this, Tclass.M3.UnionFind(), old($Heap));
            assume true;
            assume (forall f#0_0: ref :: 
              { read(old($Heap), f#0_0, M3.Element.c) } 
              $Is(f#0_0, Tclass.M3.Element())
                 ==> 
                Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(f#0_0)]
                   && M3.Contents.Link_q(read(old($Heap), f#0_0, M3.Element.c))
                 ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(M3.Contents.next(read(old($Heap), f#0_0, M3.Element.c)))]);
            assume M3.UnionFind.Collect#canCall(old($Heap), this);
            assume M3.UnionFind.Collect#canCall(old($Heap), this);
            // ProcessCallStmt: CheckSubrange
            C##0_0 := M3.UnionFind.Collect(old($Heap), this);
            assume true;
            assume (forall f#0_1: ref :: 
              { read($Heap, f#0_1, M3.Element.c) } 
              $Is(f#0_1, Tclass.M3.Element())
                 ==> 
                Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#0_1)]
                   && M3.Contents.Link_q(read($Heap, f#0_1, M3.Element.c))
                 ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, f#0_1, M3.Element.c)))]);
            assume M3.UnionFind.Collect#canCall($Heap, this);
            assume M3.UnionFind.Collect#canCall($Heap, this);
            // ProcessCallStmt: CheckSubrange
            C'##0_0 := M3.UnionFind.Collect($Heap, this);
            assume (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$M3.UnionFind.Reaches__Monotonic(this, d##0_0, e##0_0, r##0_0, C##0_0, C'##0_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](98,77)"} true;
        }
        else
        {
        }

        assume M3.Contents.Root_q(read($Heap, 
            $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]): ref, 
            M3.Element.c));
        assume M3.UnionFind.Reaches($LS($LS($LZ)), 
          this, 
          M3.Contents.depth(read($Heap, 
              $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]): ref, 
              M3.Element.c)), 
          f#2, 
          $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#2)]): ref, 
          M3.UnionFind.Collect($Heap, this));
        assume false;
    }
    else
    {
        assume (forall f#3: ref :: 
          { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#3)]): ref } 
            { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#3)] } 
          $Is(f#3, Tclass.M3.Element())
               && Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(f#3)]
             ==> M3.Contents.Root_q(read($Heap, 
                  $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#3)]): ref, 
                  M3.Element.c))
               && M3.UnionFind.Reaches($LS($LZ), 
                this, 
                M3.Contents.depth(read($Heap, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#3)]): ref, 
                    M3.Element.c)), 
                f#3, 
                $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(f#3)]): ref, 
                M3.UnionFind.Collect($Heap, this)));
    }

    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](100,6)"} true;
    assert defass#e#0;
}



procedure CheckWellformed$$M3.UnionFind.Union(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e0#0: ref
       where $Is(e0#0, Tclass.M3.Element()) && $IsAlloc(e0#0, Tclass.M3.Element(), $Heap), 
    e1#0: ref
       where $Is(e1#0, Tclass.M3.Element()) && $IsAlloc(e1#0, Tclass.M3.Element(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$M3.UnionFind.Union(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e0#0: ref
       where $Is(e0#0, Tclass.M3.Element()) && $IsAlloc(e0#0, Tclass.M3.Element(), $Heap), 
    e1#0: ref
       where $Is(e1#0, Tclass.M3.Element()) && $IsAlloc(e1#0, Tclass.M3.Element(), $Heap))
   returns (r#0: ref
       where $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap));
  // user-defined preconditions
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#2: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]): ref } 
            $Is(e#2, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#2)]]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#3: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)] } 
            $Is(e#3, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#3)]): ref));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#4: ref :: 
            { read($Heap, e#4, M3.Element.c) } 
            $Is(e#4, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
                 && M3.Contents.Link_q(read($Heap, e#4, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#4, M3.Element.c)))]));
  requires M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#5: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)] } 
            $Is(e#5, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref, 
                        M3.Element.c)), 
                    e#5, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e0#0)];
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e1#0)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  free ensures M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(r#0)];
  ensures $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(r#0)]): ref
       == $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e0#0)]): ref
     || $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(r#0)]): ref
       == $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e1#0)]): ref;
  free ensures true;
  ensures Map#Equal(read($Heap, this, M3.UnionFind.M), 
    Map#Glue((lambda $w#1: Box :: 
        $Is($Unbox($w#1): ref, Tclass.M3.Element?())
           && Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$w#1]), 
      (lambda $w#1: Box :: 
        $Box((if $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#1]): ref
                 == $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e0#0)]): ref
               || $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#1]): ref
                 == $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e1#0)]): ref
             then r#0
             else $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#1]): ref))), 
      TMap(Tclass.M3.Element?(), Tclass.M3.Element?())));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$M3.UnionFind.Union(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap), 
    e0#0: ref
       where $Is(e0#0, Tclass.M3.Element()) && $IsAlloc(e0#0, Tclass.M3.Element(), $Heap), 
    e1#0: ref
       where $Is(e1#0, Tclass.M3.Element()) && $IsAlloc(e1#0, Tclass.M3.Element(), $Heap))
   returns (defass#r#0: bool, 
    r#0: ref
       where defass#r#0
         ==> $Is(r#0, Tclass.M3.Element()) && $IsAlloc(r#0, Tclass.M3.Element(), $Heap), 
    $_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  // user-defined preconditions
  free requires M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e0#0)];
  requires Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e1#0)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#14: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]): ref } 
            $Is(e#14, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#14)]]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#15: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#15)] } 
            $Is(e#15, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#15)]): ref));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#16: ref :: 
            { read($Heap, e#16, M3.Element.c) } 
            $Is(e#16, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#16)]
                 && M3.Contents.Link_q(read($Heap, e#16, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#16, M3.Element.c)))]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#17: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#17)] } 
            $Is(e#17, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]): ref, 
                        M3.Element.c)), 
                    e#17, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#17)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  free ensures true;
  ensures $_reverifyPost
     ==> (forall $o: ref :: 
      { read(old($Heap), $o, alloc) } 
      read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
           && !read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures $_reverifyPost ==> Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$Box(r#0)];
  ensures $_reverifyPost
     ==> $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(r#0)]): ref
         == $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e0#0)]): ref
       || $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(r#0)]): ref
         == $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e1#0)]): ref;
  free ensures true;
  ensures $_reverifyPost
     ==> Map#Equal(read($Heap, this, M3.UnionFind.M), 
      Map#Glue((lambda $w#2: Box :: 
          $Is($Unbox($w#2): ref, Tclass.M3.Element?())
             && Map#Domain(read(old($Heap), this, M3.UnionFind.M))[$w#2]), 
        (lambda $w#2: Box :: 
          $Box((if $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#2]): ref
                   == $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e0#0)]): ref
                 || $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#2]): ref
                   == $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$Box(e1#0)]): ref
               then r#0
               else $Unbox(Map#Elements(read(old($Heap), this, M3.UnionFind.M))[$w#2]): ref))), 
        TMap(Tclass.M3.Element?(), Tclass.M3.Element?())));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || read(old($Heap), this, M3.UnionFind.Repr)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$M3.UnionFind.Union(this: ref, e0#0: ref, e1#0: ref)
   returns (defass#r#0: bool, r#0: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var r0#0: ref
     where $Is(r0#0, Tclass.M3.Element()) && $IsAlloc(r0#0, Tclass.M3.Element(), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass.M3.Element())
       && $IsAlloc($rhs##0, Tclass.M3.Element(), $Heap);
  var e##0: ref;
  var r1#0: ref
     where $Is(r1#0, Tclass.M3.Element()) && $IsAlloc(r1#0, Tclass.M3.Element(), $Heap);
  var $rhs##1: ref
     where $Is($rhs##1, Tclass.M3.Element())
       && $IsAlloc($rhs##1, Tclass.M3.Element(), $Heap);
  var e##1: ref;
  var $rhs##2: ref
     where $Is($rhs##2, Tclass.M3.Element())
       && $IsAlloc($rhs##2, Tclass.M3.Element(), $Heap);
  var r0##0: ref;
  var r1##0: ref;

    // AddMethodImpl: Union, Impl$$M3.UnionFind.Union
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> read($Heap, this, M3.UnionFind.Repr)[$Box($o)]);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](104,4): initial state"} true;
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](105,21)
    assume true;
    // TrCallStmt: Adding lhs with type Element
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##0 := e0#0;
    assume (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$M3.UnionFind.Find(this, e##0);
    // TrCallStmt: After ProcessCallStmt
    r0#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](105,24)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](106,21)
    assume true;
    // TrCallStmt: Adding lhs with type Element
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    e##1 := e1#0;
    assume (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##1 := Call$$M3.UnionFind.Find(this, e##1);
    // TrCallStmt: After ProcessCallStmt
    r1#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](106,24)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](107,16)
    assume true;
    // TrCallStmt: Adding lhs with type Element
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    r0##0 := r0#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    r1##0 := r1#0;
    assume (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && read($Heap, $o, alloc)
           && read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##2 := Call$$M3.UnionFind.Join(this, r0##0, r1##0);
    // TrCallStmt: After ProcessCallStmt
    r#0 := $rhs##2;
    defass#r#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](107,23)"} true;
    assert defass#r#0;
}



const M3.UnionFind.M: Field (Map Box Box);

// UnionFind.M: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M3.UnionFind.M) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.M3.UnionFind?()
     ==> $Is(read($h, $o, M3.UnionFind.M), TMap(Tclass.M3.Element(), Tclass.M3.Element())));

// UnionFind.M: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M3.UnionFind.M) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.M3.UnionFind?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, M3.UnionFind.M), TMap(Tclass.M3.Element(), Tclass.M3.Element()), $h));

// function declaration for M3.UnionFind.Valid
function M3.UnionFind.Valid($heap: Heap, this: ref) : bool;

function M3.UnionFind.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for M3.UnionFind.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), M3.UnionFind.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.M3.UnionFind())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && ($o == this || read($h0, this, M3.UnionFind.Repr)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> M3.UnionFind.Valid($h0, this) == M3.UnionFind.Valid($h1, this));

// consequence axiom for M3.UnionFind.Valid
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { M3.UnionFind.Valid($Heap, this) } 
    M3.UnionFind.Valid#canCall($Heap, this)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap))
       ==> 
      M3.UnionFind.Valid($Heap, this)
       ==> read($Heap, this, M3.UnionFind.Repr)[$Box(this)]);

function M3.UnionFind.Valid#requires(Heap, ref) : bool;

// #requires axiom for M3.UnionFind.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { M3.UnionFind.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.M3.UnionFind())
       && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap)
     ==> M3.UnionFind.Valid#requires($Heap, this) == true);

// definition axiom for M3.UnionFind.Valid (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { M3.UnionFind.Valid($Heap, this), $IsGoodHeap($Heap) } 
    M3.UnionFind.Valid#canCall($Heap, this)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.M3.UnionFind())
           && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap))
       ==> (read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
           ==> 
          !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
           ==> M3.UnionFind.ValidM1#canCall($Heap, this))
         && M3.UnionFind.Valid($Heap, this)
           == (
            read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
             && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
             && M3.UnionFind.ValidM1($Heap, this)));

procedure CheckWellformed$$M3.UnionFind.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$M3.UnionFind.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$M3.UnionFind.__ctor()
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass.M3.UnionFind())
         && $IsAlloc(this, Tclass.M3.UnionFind(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  free ensures M3.UnionFind.Valid#canCall($Heap, this)
     && 
    M3.UnionFind.Valid($Heap, this)
     && 
    read($Heap, this, M3.UnionFind.Repr)[$Box(this)]
     && !read($Heap, this, M3.UnionFind.Repr)[$Box(null)]
     && M3.UnionFind.ValidM1($Heap, this);
  free ensures true;
  ensures (forall $o: ref :: 
    { read($Heap, this, M3.UnionFind.Repr)[$Box($o)] } 
    read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures Map#Equal(read($Heap, this, M3.UnionFind.M), Map#Empty(): Map Box Box);
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$M3.UnionFind.__ctor()
   returns (this: ref where this != null && $Is(this, Tclass.M3.UnionFind()), 
    $_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures M3.UnionFind.Valid#canCall($Heap, this);
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || read($Heap, this, M3.UnionFind.Repr)[$Box(this)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || !read($Heap, this, M3.UnionFind.Repr)[$Box(null)];
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || Set#Subset(Map#Domain(read($Heap, this, M3.UnionFind.M)), 
            read($Heap, this, M3.UnionFind.Repr)));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#4: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]): ref } 
            $Is(e#4, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#4)]]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#5: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)] } 
            $Is(e#5, Tclass.M3.Element?())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]
               ==> $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]]): ref
                 == $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#5)]): ref));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#6: ref :: 
            { read($Heap, e#6, M3.Element.c) } 
            $Is(e#6, Tclass.M3.Element())
               ==> 
              Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#6)]
                 && M3.Contents.Link_q(read($Heap, e#6, M3.Element.c))
               ==> Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(M3.Contents.next(read($Heap, e#6, M3.Element.c)))]));
  ensures $_reverifyPost
     ==> 
    M3.UnionFind.Valid#canCall($Heap, this)
     ==> M3.UnionFind.Valid($Heap, this)
       || (M3.UnionFind.ValidM1#canCall($Heap, this)
         ==> M3.UnionFind.ValidM1($Heap, this)
           || (forall e#7: ref :: 
            { $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#7)]): ref } 
              { Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#7)] } 
            $Is(e#7, Tclass.M3.Element())
               ==> (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#7)]
                   ==> M3.Contents.Root_q(read($Heap, 
                      $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#7)]): ref, 
                      M3.Element.c)))
                 && (Map#Domain(read($Heap, this, M3.UnionFind.M))[$Box(e#7)]
                   ==> M3.UnionFind.Reaches($LS($LS($LZ)), 
                    this, 
                    M3.Contents.depth(read($Heap, 
                        $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#7)]): ref, 
                        M3.Element.c)), 
                    e#7, 
                    $Unbox(Map#Elements(read($Heap, this, M3.UnionFind.M))[$Box(e#7)]): ref, 
                    M3.UnionFind.Collect($Heap, this)))));
  free ensures true;
  ensures $_reverifyPost
     ==> (forall $o: ref :: 
      { read($Heap, this, M3.UnionFind.Repr)[$Box($o)] } 
      read($Heap, this, M3.UnionFind.Repr)[$Box($o)]
         ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures $_reverifyPost
     ==> Map#Equal(read($Heap, this, M3.UnionFind.M), Map#Empty(): Map Box Box);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$M3.UnionFind.__ctor() returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.M: Map Box Box;
  var this.Repr: Set Box;
  var $obj0: ref;
  var $obj1: ref;
  var $rhs#0: Set Box where $Is($rhs#0, TSet(Tclass._System.object?()));
  var $rhs#1: Map Box Box
     where $Is($rhs#1, TMap(Tclass.M3.Element(), Tclass.M3.Element()));
  var $rhs#2: Set Box where $Is($rhs#2, TSet(Tclass._System.object?()));

    // AddMethodImpl: _ctor, Impl$$M3.UnionFind.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M1][M2][M3](20,4): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M1][M2][M3](20,5)
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M1][M2][M3](21,15)
    assume true;
    $obj0 := this;
    assume true;
    $obj1 := this;
    assume true;
    assume $Is(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), TSet(Tclass._System.object?()));
    $rhs#0 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    assume true;
    $rhs#1 := Lit(Map#Empty(): Map Box Box);
    this.Repr := $rhs#0;
    this.M := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M1][M2][M3](21,30)"} true;
    // ----- new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M1][M2][M3](20,5)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, M3.UnionFind.M) == this.M;
    assume read($Heap, this, M3.UnionFind.Repr) == this.Repr;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M1][M2][M3](20,5)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M1][M2][M3](18,5)
    assume true;
    assume $_Frame[this, M3.UnionFind.Repr];
    assume true;
    assume $Is(Set#UnionOne(Set#Empty(): Set Box, $Box(this)), TSet(Tclass._System.object?()));
    $rhs#2 := Set#UnionOne(Set#Empty(): Set Box, $Box(this));
    $Heap := update($Heap, this, M3.UnionFind.Repr, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M1][M2][M3](18,4)"} true;
}



const M3.UnionFind.Repr: Field (Set Box);

// UnionFind.Repr: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M3.UnionFind.Repr) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.M3.UnionFind?()
     ==> $Is(read($h, $o, M3.UnionFind.Repr), TSet(Tclass._System.object?())));

// UnionFind.Repr: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M3.UnionFind.Repr) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.M3.UnionFind?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, M3.UnionFind.Repr), TSet(Tclass._System.object?()), $h));

// M3.UnionFind: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.M3.UnionFind()) } 
  $Is(c#0, Tclass.M3.UnionFind())
     <==> $Is(c#0, Tclass.M3.UnionFind?()) && c#0 != null);

// M3.UnionFind: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.M3.UnionFind(), $h) } 
  $IsAlloc(c#0, Tclass.M3.UnionFind(), $h)
     <==> $IsAlloc(c#0, Tclass.M3.UnionFind?(), $h));

const unique class.M3.__default: ClassName;

function Tclass.M3.__default() : Ty;

const unique Tagclass.M3.__default: TyTag;

// Tclass.M3.__default Tag
axiom Tag(Tclass.M3.__default()) == Tagclass.M3.__default
   && TagFamily(Tclass.M3.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.M3.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M3.__default()) } 
  $IsBox(bx, Tclass.M3.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M3.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M3.__default()) } 
  $Is($o, Tclass.M3.__default())
     <==> $o == null || dtype($o) == Tclass.M3.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M3.__default(), $h) } 
  $IsAlloc($o, Tclass.M3.__default(), $h) <==> $o == null || read($h, $o, alloc));

// function declaration for M3._default.GoodCMap
function M3.__default.GoodCMap(C#0: Map Box Box) : bool;

function M3.__default.GoodCMap#canCall(C#0: Map Box Box) : bool;

// consequence axiom for M3.__default.GoodCMap
axiom 4 <= $FunctionContextHeight
   ==> (forall C#0: Map Box Box :: 
    { M3.__default.GoodCMap(C#0) } 
    M3.__default.GoodCMap#canCall(C#0)
         || (4 != $FunctionContextHeight
           && $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents())))
       ==> true);

function M3.__default.GoodCMap#requires(Map Box Box) : bool;

// #requires axiom for M3.__default.GoodCMap
axiom (forall C#0: Map Box Box :: 
  { M3.__default.GoodCMap#requires(C#0) } 
  $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents()))
     ==> M3.__default.GoodCMap#requires(C#0) == true);

// definition axiom for M3.__default.GoodCMap (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall C#0: Map Box Box :: 
    { M3.__default.GoodCMap(C#0) } 
    M3.__default.GoodCMap#canCall(C#0)
         || (4 != $FunctionContextHeight
           && $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents())))
       ==> M3.__default.GoodCMap(C#0)
         == (forall f#0: ref :: 
          { $Unbox(Map#Elements(C#0)[$Box(f#0)]): DatatypeType } 
          $Is(f#0, Tclass.M3.Element?())
             ==> 
            Map#Domain(C#0)[$Box(f#0)]
               && M3.Contents.Link_q($Unbox(Map#Elements(C#0)[$Box(f#0)]): DatatypeType)
             ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(C#0)[$Box(f#0)]): DatatypeType))]));

// definition axiom for M3.__default.GoodCMap for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall C#0: Map Box Box :: 
    {:weight 3} { M3.__default.GoodCMap(Lit(C#0)) } 
    M3.__default.GoodCMap#canCall(Lit(C#0))
         || (4 != $FunctionContextHeight
           && $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents())))
       ==> M3.__default.GoodCMap(Lit(C#0))
         == (forall f#1: ref :: 
          { $Unbox(Map#Elements(C#0)[$Box(f#1)]): DatatypeType } 
          $Is(f#1, Tclass.M3.Element?())
             ==> 
            Map#Domain(C#0)[$Box(f#1)]
               && M3.Contents.Link_q($Unbox(Map#Elements(Lit(C#0))[$Box(f#1)]): DatatypeType)
             ==> Map#Domain(C#0)[$Box(M3.Contents.next($Unbox(Map#Elements(Lit(C#0))[$Box(f#1)]): DatatypeType))]));

procedure CheckWellformed$$M3.__default.GoodCMap(C#0: Map Box Box where $Is(C#0, TMap(Tclass.M3.Element(), Tclass.M3.Contents())));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$M3.__default.MapsEqual(M3._default.MapsEqual$D: Ty, 
    m#0: Map Box Box
       where $Is(m#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D))
         && $IsAlloc(m#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D), $Heap), 
    n#0: Map Box Box
       where $Is(n#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D))
         && $IsAlloc(n#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D), $Heap));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$M3.__default.MapsEqual(M3._default.MapsEqual$D: Ty, 
    m#0: Map Box Box
       where $Is(m#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D))
         && $IsAlloc(m#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D), $Heap), 
    n#0: Map Box Box
       where $Is(n#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D))
         && $IsAlloc(n#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D), $Heap));
  // user-defined preconditions
  requires (forall d#1: Box :: 
    { Map#Domain(n#0)[d#1] } { Map#Domain(m#0)[d#1] } 
    $IsBox(d#1, M3._default.MapsEqual$D)
       ==> (Map#Domain(m#0)[d#1] <==> Map#Domain(n#0)[d#1]));
  requires (forall d#3: Box :: 
    { Map#Elements(n#0)[d#3] } { Map#Elements(m#0)[d#3] } { Map#Domain(m#0)[d#3] } 
    $IsBox(d#3, M3._default.MapsEqual$D)
       ==> 
      Map#Domain(m#0)[d#3]
       ==> Map#Elements(m#0)[d#3] == Map#Elements(n#0)[d#3]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Map#Equal(m#0, n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$M3.__default.MapsEqual(M3._default.MapsEqual$D: Ty, 
    m#0: Map Box Box
       where $Is(m#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D))
         && $IsAlloc(m#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D), $Heap), 
    n#0: Map Box Box
       where $Is(n#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D))
         && $IsAlloc(n#0, TMap(M3._default.MapsEqual$D, M3._default.MapsEqual$D), $Heap))
   returns ($_reverifyPost: bool);
  free requires 9 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall d#1: Box :: 
    { Map#Domain(n#0)[d#1] } { Map#Domain(m#0)[d#1] } 
    $IsBox(d#1, M3._default.MapsEqual$D)
       ==> (Map#Domain(m#0)[d#1] <==> Map#Domain(n#0)[d#1]));
  requires (forall d#3: Box :: 
    { Map#Elements(n#0)[d#3] } { Map#Elements(m#0)[d#3] } { Map#Domain(m#0)[d#3] } 
    $IsBox(d#3, M3._default.MapsEqual$D)
       ==> 
      Map#Domain(m#0)[d#3]
       ==> Map#Elements(m#0)[d#3] == Map#Elements(n#0)[d#3]);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures $_reverifyPost ==> Map#Equal(m#0, n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$M3.__default.MapsEqual(M3._default.MapsEqual$D: Ty, m#0: Map Box Box, n#0: Map Box Box)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: MapsEqual, Impl$$M3.__default.MapsEqual
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny4/UnionFind.dfy[M2][M3](121,2): initial state"} true;
    $_reverifyPost := false;
}



// Constructor function declaration
function #M3.Contents.Root(int) : DatatypeType;

const unique ##M3.Contents.Root: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: int :: 
  { #M3.Contents.Root(a#0#0#0) } 
  DatatypeCtorId(#M3.Contents.Root(a#0#0#0)) == ##M3.Contents.Root);

function M3.Contents.Root_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { M3.Contents.Root_q(d) } 
  M3.Contents.Root_q(d) <==> DatatypeCtorId(d) == ##M3.Contents.Root);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { M3.Contents.Root_q(d) } 
  M3.Contents.Root_q(d)
     ==> (exists a#1#0#0: int :: d == #M3.Contents.Root(a#1#0#0)));

// Constructor $Is
axiom (forall a#2#0#0: int :: 
  { $Is(#M3.Contents.Root(a#2#0#0), Tclass.M3.Contents()) } 
  $Is(#M3.Contents.Root(a#2#0#0), Tclass.M3.Contents())
     <==> $Is(a#2#0#0, Tclass._System.nat()));

// Constructor $IsAlloc
axiom (forall a#3#0#0: int, $h: Heap :: 
  { $IsAlloc(#M3.Contents.Root(a#3#0#0), Tclass.M3.Contents(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#M3.Contents.Root(a#3#0#0), Tclass.M3.Contents(), $h)
       <==> $IsAlloc(a#3#0#0, Tclass._System.nat(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(M3.Contents.depth(d), Tclass._System.nat(), $h) } 
  $IsGoodHeap($h)
       && 
      M3.Contents.Root_q(d)
       && $IsAlloc(d, Tclass.M3.Contents(), $h)
     ==> $IsAlloc(M3.Contents.depth(d), Tclass._System.nat(), $h));

// Constructor literal
axiom (forall a#4#0#0: int :: 
  { #M3.Contents.Root(LitInt(a#4#0#0)) } 
  #M3.Contents.Root(LitInt(a#4#0#0)) == Lit(#M3.Contents.Root(a#4#0#0)));

function M3.Contents.depth(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#5#0#0: int :: 
  { #M3.Contents.Root(a#5#0#0) } 
  M3.Contents.depth(#M3.Contents.Root(a#5#0#0)) == a#5#0#0);

// Constructor function declaration
function #M3.Contents.Link(ref) : DatatypeType;

const unique ##M3.Contents.Link: DtCtorId;

// Constructor identifier
axiom (forall a#6#0#0: ref :: 
  { #M3.Contents.Link(a#6#0#0) } 
  DatatypeCtorId(#M3.Contents.Link(a#6#0#0)) == ##M3.Contents.Link);

function M3.Contents.Link_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { M3.Contents.Link_q(d) } 
  M3.Contents.Link_q(d) <==> DatatypeCtorId(d) == ##M3.Contents.Link);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { M3.Contents.Link_q(d) } 
  M3.Contents.Link_q(d)
     ==> (exists a#7#0#0: ref :: d == #M3.Contents.Link(a#7#0#0)));

// Constructor $Is
axiom (forall a#8#0#0: ref :: 
  { $Is(#M3.Contents.Link(a#8#0#0), Tclass.M3.Contents()) } 
  $Is(#M3.Contents.Link(a#8#0#0), Tclass.M3.Contents())
     <==> $Is(a#8#0#0, Tclass.M3.Element()));

// Constructor $IsAlloc
axiom (forall a#9#0#0: ref, $h: Heap :: 
  { $IsAlloc(#M3.Contents.Link(a#9#0#0), Tclass.M3.Contents(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#M3.Contents.Link(a#9#0#0), Tclass.M3.Contents(), $h)
       <==> $IsAlloc(a#9#0#0, Tclass.M3.Element(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(M3.Contents.next(d), Tclass.M3.Element(), $h) } 
  $IsGoodHeap($h)
       && 
      M3.Contents.Link_q(d)
       && $IsAlloc(d, Tclass.M3.Contents(), $h)
     ==> $IsAlloc(M3.Contents.next(d), Tclass.M3.Element(), $h));

// Constructor literal
axiom (forall a#10#0#0: ref :: 
  { #M3.Contents.Link(Lit(a#10#0#0)) } 
  #M3.Contents.Link(Lit(a#10#0#0)) == Lit(#M3.Contents.Link(a#10#0#0)));

function M3.Contents.next(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#11#0#0: ref :: 
  { #M3.Contents.Link(a#11#0#0) } 
  M3.Contents.next(#M3.Contents.Link(a#11#0#0)) == a#11#0#0);

// Depth-one case-split function
function $IsA#M3.Contents(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#M3.Contents(d) } 
  $IsA#M3.Contents(d) ==> M3.Contents.Root_q(d) || M3.Contents.Link_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { M3.Contents.Link_q(d), $Is(d, Tclass.M3.Contents()) } 
    { M3.Contents.Root_q(d), $Is(d, Tclass.M3.Contents()) } 
  $Is(d, Tclass.M3.Contents()) ==> M3.Contents.Root_q(d) || M3.Contents.Link_q(d));

// Datatype extensional equality declaration
function M3.Contents#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #M3.Contents.Root
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M3.Contents#Equal(a, b), M3.Contents.Root_q(a) } 
    { M3.Contents#Equal(a, b), M3.Contents.Root_q(b) } 
  M3.Contents.Root_q(a) && M3.Contents.Root_q(b)
     ==> (M3.Contents#Equal(a, b) <==> M3.Contents.depth(a) == M3.Contents.depth(b)));

// Datatype extensional equality definition: #M3.Contents.Link
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M3.Contents#Equal(a, b), M3.Contents.Link_q(a) } 
    { M3.Contents#Equal(a, b), M3.Contents.Link_q(b) } 
  M3.Contents.Link_q(a) && M3.Contents.Link_q(b)
     ==> (M3.Contents#Equal(a, b) <==> M3.Contents.next(a) == M3.Contents.next(b)));

// Datatype extensionality axiom: M3.Contents
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { M3.Contents#Equal(a, b) } 
  M3.Contents#Equal(a, b) <==> a == b);

const unique class.M3.Contents: ClassName;

const unique class.M3.Element?: ClassName;

// Element: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M3.Element?()) } 
  $Is($o, Tclass.M3.Element?())
     <==> $o == null || dtype($o) == Tclass.M3.Element?());

// Element: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M3.Element?(), $h) } 
  $IsAlloc($o, Tclass.M3.Element?(), $h) <==> $o == null || read($h, $o, alloc));

const M3.Element.c: Field DatatypeType;

// Element.c: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M3.Element.c) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.M3.Element?()
     ==> $Is(read($h, $o, M3.Element.c), Tclass.M3.Contents()));

// Element.c: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, M3.Element.c) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.M3.Element?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, M3.Element.c), Tclass.M3.Contents(), $h));

// M3.Element: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.M3.Element()) } 
  $Is(c#0, Tclass.M3.Element()) <==> $Is(c#0, Tclass.M3.Element?()) && c#0 != null);

// M3.Element: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.M3.Element(), $h) } 
  $IsAlloc(c#0, Tclass.M3.Element(), $h)
     <==> $IsAlloc(c#0, Tclass.M3.Element?(), $h));

const unique tytagFamily$nat: TyTagFamily;

const unique tytagFamily$object: TyTagFamily;

const unique tytagFamily$array: TyTagFamily;

const unique tytagFamily$_#Func1: TyTagFamily;

const unique tytagFamily$_#PartialFunc1: TyTagFamily;

const unique tytagFamily$_#TotalFunc1: TyTagFamily;

const unique tytagFamily$_#Func0: TyTagFamily;

const unique tytagFamily$_#PartialFunc0: TyTagFamily;

const unique tytagFamily$_#TotalFunc0: TyTagFamily;

const unique tytagFamily$_#Func4: TyTagFamily;

const unique tytagFamily$_#PartialFunc4: TyTagFamily;

const unique tytagFamily$_#TotalFunc4: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$UnionFind: TyTagFamily;

const unique tytagFamily$Element: TyTagFamily;

const unique tytagFamily$Contents: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$Repr: NameFamily;

const unique field$M: NameFamily;

const unique field$c: NameFamily;
