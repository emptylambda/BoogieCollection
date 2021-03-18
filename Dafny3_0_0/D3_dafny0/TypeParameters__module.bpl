// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy -print:./TypeParameters.bpl

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

const unique class._System.array2?: ClassName;

function Tclass._System.array2?(Ty) : Ty;

const unique Tagclass._System.array2?: TyTag;

// Tclass._System.array2? Tag
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2?(_System.array2$arg) } 
  Tag(Tclass._System.array2?(_System.array2$arg)) == Tagclass._System.array2?
     && TagFamily(Tclass._System.array2?(_System.array2$arg)) == tytagFamily$array2);

// Tclass._System.array2? injectivity 0
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2?(_System.array2$arg) } 
  Tclass._System.array2?_0(Tclass._System.array2?(_System.array2$arg))
     == _System.array2$arg);

function Tclass._System.array2?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array2?
axiom (forall _System.array2$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array2?(_System.array2$arg)) } 
  $IsBox(bx, Tclass._System.array2?(_System.array2$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array2?(_System.array2$arg)));

axiom (forall o: ref :: { _System.array2.Length0(o) } 0 <= _System.array2.Length0(o));

axiom (forall o: ref :: { _System.array2.Length1(o) } 0 <= _System.array2.Length1(o));

// array2.: Type axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int :: 
  { read($h, $o, MultiIndexField(IndexField($i0), $i1)), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && 
      0 <= $i0
       && $i0 < _System.array2.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array2.Length1($o)
     ==> $IsBox(read($h, $o, MultiIndexField(IndexField($i0), $i1)), _System.array2$arg));

// array2.: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int :: 
  { read($h, $o, MultiIndexField(IndexField($i0), $i1)), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && 
      0 <= $i0
       && $i0 < _System.array2.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array2.Length1($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, MultiIndexField(IndexField($i0), $i1)), _System.array2$arg, $h));

// array2: Class $Is
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array2?(_System.array2$arg)) } 
  $Is($o, Tclass._System.array2?(_System.array2$arg))
     <==> $o == null || dtype($o) == Tclass._System.array2?(_System.array2$arg));

// array2: Class $IsAlloc
axiom (forall _System.array2$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array2?(_System.array2$arg), $h) } 
  $IsAlloc($o, Tclass._System.array2?(_System.array2$arg), $h)
     <==> $o == null || read($h, $o, alloc));

function _System.array2.Length0(ref) : int;

// array2.Length0: Type axiom
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { _System.array2.Length0($o), Tclass._System.array2?(_System.array2$arg) } 
  $o != null && dtype($o) == Tclass._System.array2?(_System.array2$arg)
     ==> $Is(_System.array2.Length0($o), TInt));

// array2.Length0: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array2.Length0($o), read($h, $o, alloc), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array2.Length0($o), TInt, $h));

function _System.array2.Length1(ref) : int;

// array2.Length1: Type axiom
axiom (forall _System.array2$arg: Ty, $o: ref :: 
  { _System.array2.Length1($o), Tclass._System.array2?(_System.array2$arg) } 
  $o != null && dtype($o) == Tclass._System.array2?(_System.array2$arg)
     ==> $Is(_System.array2.Length1($o), TInt));

// array2.Length1: Allocation axiom
axiom (forall _System.array2$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array2.Length1($o), read($h, $o, alloc), Tclass._System.array2?(_System.array2$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array2?(_System.array2$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array2.Length1($o), TInt, $h));

function Tclass._System.array2(Ty) : Ty;

const unique Tagclass._System.array2: TyTag;

// Tclass._System.array2 Tag
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2(_System.array2$arg) } 
  Tag(Tclass._System.array2(_System.array2$arg)) == Tagclass._System.array2
     && TagFamily(Tclass._System.array2(_System.array2$arg)) == tytagFamily$array2);

// Tclass._System.array2 injectivity 0
axiom (forall _System.array2$arg: Ty :: 
  { Tclass._System.array2(_System.array2$arg) } 
  Tclass._System.array2_0(Tclass._System.array2(_System.array2$arg))
     == _System.array2$arg);

function Tclass._System.array2_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array2
axiom (forall _System.array2$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array2(_System.array2$arg)) } 
  $IsBox(bx, Tclass._System.array2(_System.array2$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array2(_System.array2$arg)));

// _System.array2: subset type $Is
axiom (forall _System.array2$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array2(_System.array2$arg)) } 
  $Is(c#0, Tclass._System.array2(_System.array2$arg))
     <==> $Is(c#0, Tclass._System.array2?(_System.array2$arg)) && c#0 != null);

// _System.array2: subset type $IsAlloc
axiom (forall _System.array2$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array2(_System.array2$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array2(_System.array2$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array2?(_System.array2$arg), $h));

const unique class._System.array3?: ClassName;

function Tclass._System.array3?(Ty) : Ty;

const unique Tagclass._System.array3?: TyTag;

// Tclass._System.array3? Tag
axiom (forall _System.array3$arg: Ty :: 
  { Tclass._System.array3?(_System.array3$arg) } 
  Tag(Tclass._System.array3?(_System.array3$arg)) == Tagclass._System.array3?
     && TagFamily(Tclass._System.array3?(_System.array3$arg)) == tytagFamily$array3);

// Tclass._System.array3? injectivity 0
axiom (forall _System.array3$arg: Ty :: 
  { Tclass._System.array3?(_System.array3$arg) } 
  Tclass._System.array3?_0(Tclass._System.array3?(_System.array3$arg))
     == _System.array3$arg);

function Tclass._System.array3?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array3?
axiom (forall _System.array3$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array3?(_System.array3$arg)) } 
  $IsBox(bx, Tclass._System.array3?(_System.array3$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array3?(_System.array3$arg)));

axiom (forall o: ref :: { _System.array3.Length0(o) } 0 <= _System.array3.Length0(o));

axiom (forall o: ref :: { _System.array3.Length1(o) } 0 <= _System.array3.Length1(o));

axiom (forall o: ref :: { _System.array3.Length2(o) } 0 <= _System.array3.Length2(o));

// array3.: Type axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int, $i2: int :: 
  { read($h, $o, MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2)), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && 
      0 <= $i0
       && $i0 < _System.array3.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array3.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array3.Length2($o)
     ==> $IsBox(read($h, $o, MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2)), 
      _System.array3$arg));

// array3.: Allocation axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref, $i0: int, $i1: int, $i2: int :: 
  { read($h, $o, MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2)), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && 
      0 <= $i0
       && $i0 < _System.array3.Length0($o)
       && 
      0 <= $i1
       && $i1 < _System.array3.Length1($o)
       && 
      0 <= $i2
       && $i2 < _System.array3.Length2($o)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, MultiIndexField(MultiIndexField(IndexField($i0), $i1), $i2)), 
      _System.array3$arg, 
      $h));

// array3: Class $Is
axiom (forall _System.array3$arg: Ty, $o: ref :: 
  { $Is($o, Tclass._System.array3?(_System.array3$arg)) } 
  $Is($o, Tclass._System.array3?(_System.array3$arg))
     <==> $o == null || dtype($o) == Tclass._System.array3?(_System.array3$arg));

// array3: Class $IsAlloc
axiom (forall _System.array3$arg: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._System.array3?(_System.array3$arg), $h) } 
  $IsAlloc($o, Tclass._System.array3?(_System.array3$arg), $h)
     <==> $o == null || read($h, $o, alloc));

function _System.array3.Length0(ref) : int;

// array3.Length0: Type axiom
axiom (forall _System.array3$arg: Ty, $o: ref :: 
  { _System.array3.Length0($o), Tclass._System.array3?(_System.array3$arg) } 
  $o != null && dtype($o) == Tclass._System.array3?(_System.array3$arg)
     ==> $Is(_System.array3.Length0($o), TInt));

// array3.Length0: Allocation axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array3.Length0($o), read($h, $o, alloc), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array3.Length0($o), TInt, $h));

function _System.array3.Length1(ref) : int;

// array3.Length1: Type axiom
axiom (forall _System.array3$arg: Ty, $o: ref :: 
  { _System.array3.Length1($o), Tclass._System.array3?(_System.array3$arg) } 
  $o != null && dtype($o) == Tclass._System.array3?(_System.array3$arg)
     ==> $Is(_System.array3.Length1($o), TInt));

// array3.Length1: Allocation axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array3.Length1($o), read($h, $o, alloc), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array3.Length1($o), TInt, $h));

function _System.array3.Length2(ref) : int;

// array3.Length2: Type axiom
axiom (forall _System.array3$arg: Ty, $o: ref :: 
  { _System.array3.Length2($o), Tclass._System.array3?(_System.array3$arg) } 
  $o != null && dtype($o) == Tclass._System.array3?(_System.array3$arg)
     ==> $Is(_System.array3.Length2($o), TInt));

// array3.Length2: Allocation axiom
axiom (forall _System.array3$arg: Ty, $h: Heap, $o: ref :: 
  { _System.array3.Length2($o), read($h, $o, alloc), Tclass._System.array3?(_System.array3$arg) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._System.array3?(_System.array3$arg)
       && read($h, $o, alloc)
     ==> $IsAlloc(_System.array3.Length2($o), TInt, $h));

function Tclass._System.array3(Ty) : Ty;

const unique Tagclass._System.array3: TyTag;

// Tclass._System.array3 Tag
axiom (forall _System.array3$arg: Ty :: 
  { Tclass._System.array3(_System.array3$arg) } 
  Tag(Tclass._System.array3(_System.array3$arg)) == Tagclass._System.array3
     && TagFamily(Tclass._System.array3(_System.array3$arg)) == tytagFamily$array3);

// Tclass._System.array3 injectivity 0
axiom (forall _System.array3$arg: Ty :: 
  { Tclass._System.array3(_System.array3$arg) } 
  Tclass._System.array3_0(Tclass._System.array3(_System.array3$arg))
     == _System.array3$arg);

function Tclass._System.array3_0(Ty) : Ty;

// Box/unbox axiom for Tclass._System.array3
axiom (forall _System.array3$arg: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._System.array3(_System.array3$arg)) } 
  $IsBox(bx, Tclass._System.array3(_System.array3$arg))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._System.array3(_System.array3$arg)));

// _System.array3: subset type $Is
axiom (forall _System.array3$arg: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._System.array3(_System.array3$arg)) } 
  $Is(c#0, Tclass._System.array3(_System.array3$arg))
     <==> $Is(c#0, Tclass._System.array3?(_System.array3$arg)) && c#0 != null);

// _System.array3: subset type $IsAlloc
axiom (forall _System.array3$arg: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._System.array3(_System.array3$arg), $h) } 
  $IsAlloc(c#0, Tclass._System.array3(_System.array3$arg), $h)
     <==> $IsAlloc(c#0, Tclass._System.array3?(_System.array3$arg), $h));

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

const BaseFuel_ParseGenerics._default.Many: LayerType;

const StartFuel_ParseGenerics._default.Many: LayerType;

const StartFuelAssert_ParseGenerics._default.Many: LayerType;

const unique class._module.C?: ClassName;

function Tclass._module.C?(Ty) : Ty;

const unique Tagclass._module.C?: TyTag;

// Tclass._module.C? Tag
axiom (forall _module.C$U: Ty :: 
  { Tclass._module.C?(_module.C$U) } 
  Tag(Tclass._module.C?(_module.C$U)) == Tagclass._module.C?
     && TagFamily(Tclass._module.C?(_module.C$U)) == tytagFamily$C);

// Tclass._module.C? injectivity 0
axiom (forall _module.C$U: Ty :: 
  { Tclass._module.C?(_module.C$U) } 
  Tclass._module.C?_0(Tclass._module.C?(_module.C$U)) == _module.C$U);

function Tclass._module.C?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.C?
axiom (forall _module.C$U: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.C?(_module.C$U)) } 
  $IsBox(bx, Tclass._module.C?(_module.C$U))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.C?(_module.C$U)));

// C: Class $Is
axiom (forall _module.C$U: Ty, $o: ref :: 
  { $Is($o, Tclass._module.C?(_module.C$U)) } 
  $Is($o, Tclass._module.C?(_module.C$U))
     <==> $o == null || dtype($o) == Tclass._module.C?(_module.C$U));

// C: Class $IsAlloc
axiom (forall _module.C$U: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.C?(_module.C$U), $h) } 
  $IsAlloc($o, Tclass._module.C?(_module.C$U), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.C(Ty) : Ty;

const unique Tagclass._module.C: TyTag;

// Tclass._module.C Tag
axiom (forall _module.C$U: Ty :: 
  { Tclass._module.C(_module.C$U) } 
  Tag(Tclass._module.C(_module.C$U)) == Tagclass._module.C
     && TagFamily(Tclass._module.C(_module.C$U)) == tytagFamily$C);

// Tclass._module.C injectivity 0
axiom (forall _module.C$U: Ty :: 
  { Tclass._module.C(_module.C$U) } 
  Tclass._module.C_0(Tclass._module.C(_module.C$U)) == _module.C$U);

function Tclass._module.C_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.C
axiom (forall _module.C$U: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.C(_module.C$U)) } 
  $IsBox(bx, Tclass._module.C(_module.C$U))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.C(_module.C$U)));

procedure CheckWellformed$$_module.C.M(_module.C$U: Ty, 
    _module.C.M$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.C.M$T) && $IsAllocBox(x#0, _module.C.M$T, $Heap), 
    u#0: Box where $IsBox(u#0, _module.C$U) && $IsAllocBox(u#0, _module.C$U, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module.C.M$T) && $IsAllocBox(y#0, _module.C.M$T, $Heap));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.C.M(_module.C$U: Ty, 
    _module.C.M$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.C.M$T) && $IsAllocBox(x#0, _module.C.M$T, $Heap), 
    u#0: Box where $IsBox(u#0, _module.C$U) && $IsAllocBox(u#0, _module.C$U, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module.C.M$T) && $IsAllocBox(y#0, _module.C.M$T, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == y#0;
  ensures u#0 == u#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.C.M(_module.C$U: Ty, 
    _module.C.M$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.C.M$T) && $IsAllocBox(x#0, _module.C.M$T, $Heap), 
    u#0: Box where $IsBox(u#0, _module.C$U) && $IsAllocBox(u#0, _module.C$U, $Heap))
   returns (defass#y#0: bool, 
    y#0: Box
       where defass#y#0
         ==> $IsBox(y#0, _module.C.M$T) && $IsAllocBox(y#0, _module.C.M$T, $Heap), 
    $_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures x#0 == y#0;
  ensures u#0 == u#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.C.M(_module.C$U: Ty, _module.C.M$T: Ty, this: ref, x#0: Box, u#0: Box)
   returns (defass#y#0: bool, y#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, Impl$$_module.C.M
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(7,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(8,7)
    assume true;
    assume true;
    y#0 := x#0;
    defass#y#0 := true;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(8,10)"} true;
    assert defass#y#0;
}



// function declaration for _module.C.F
function _module.C.F(_module.C$U: Ty, _module.C.F$X: Ty, this: ref, x#0: Box, u#0: Box) : bool;

function _module.C.F#canCall(_module.C$U: Ty, _module.C.F$X: Ty, this: ref, x#0: Box, u#0: Box) : bool;

// consequence axiom for _module.C.F
axiom 15 <= $FunctionContextHeight
   ==> (forall _module.C$U: Ty, _module.C.F$X: Ty, this: ref, x#0: Box, u#0: Box :: 
    { _module.C.F(_module.C$U, _module.C.F$X, this, x#0, u#0) } 
    _module.C.F#canCall(_module.C$U, _module.C.F$X, this, x#0, u#0)
         || (15 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.C(_module.C$U))
           && $IsBox(x#0, _module.C.F$X)
           && $IsBox(u#0, _module.C$U))
       ==> true);

function _module.C.F#requires(Ty, Ty, ref, Box, Box) : bool;

// #requires axiom for _module.C.F
axiom (forall _module.C$U: Ty, _module.C.F$X: Ty, this: ref, x#0: Box, u#0: Box :: 
  { _module.C.F#requires(_module.C$U, _module.C.F$X, this, x#0, u#0) } 
  this != null
       && $Is(this, Tclass._module.C(_module.C$U))
       && $IsBox(x#0, _module.C.F$X)
       && $IsBox(u#0, _module.C$U)
     ==> _module.C.F#requires(_module.C$U, _module.C.F$X, this, x#0, u#0) == true);

// definition axiom for _module.C.F (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall _module.C$U: Ty, _module.C.F$X: Ty, this: ref, x#0: Box, u#0: Box :: 
    { _module.C.F(_module.C$U, _module.C.F$X, this, x#0, u#0) } 
    _module.C.F#canCall(_module.C$U, _module.C.F$X, this, x#0, u#0)
         || (15 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.C(_module.C$U))
           && $IsBox(x#0, _module.C.F$X)
           && $IsBox(u#0, _module.C$U))
       ==> _module.C.F(_module.C$U, _module.C.F$X, this, x#0, u#0)
         == (x#0 == x#0 && u#0 == u#0));

// definition axiom for _module.C.F for all literals (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall _module.C$U: Ty, _module.C.F$X: Ty, this: ref, x#0: Box, u#0: Box :: 
    {:weight 3} { _module.C.F(_module.C$U, _module.C.F$X, Lit(this), Lit(x#0), Lit(u#0)) } 
    _module.C.F#canCall(_module.C$U, _module.C.F$X, Lit(this), Lit(x#0), Lit(u#0))
         || (15 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.C(_module.C$U))
           && $IsBox(x#0, _module.C.F$X)
           && $IsBox(u#0, _module.C$U))
       ==> _module.C.F(_module.C$U, _module.C.F$X, Lit(this), Lit(x#0), Lit(u#0))
         == (Lit(x#0) == Lit(x#0) && Lit(u#0) == Lit(u#0)));

procedure CheckWellformed$$_module.C.F(_module.C$U: Ty, 
    _module.C.F$X: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap), 
    x#0: Box where $IsBox(x#0, _module.C.F$X), 
    u#0: Box where $IsBox(u#0, _module.C$U));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.C.Main(_module.C$U: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap), 
    u#0: Box where $IsBox(u#0, _module.C$U) && $IsAllocBox(u#0, _module.C$U, $Heap));
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.C.Main(_module.C$U: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap), 
    u#0: Box where $IsBox(u#0, _module.C$U) && $IsAllocBox(u#0, _module.C$U, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.C.Main(_module.C$U: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap), 
    u#0: Box where $IsBox(u#0, _module.C$U) && $IsAllocBox(u#0, _module.C$U, $Heap))
   returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.C.Main(_module.C$U: Ty, this: ref, u#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var t#0: bool;
  var ##x#0: int;
  var ##u#0: Box;
  var ##x#1: ref;
  var ##u#1: Box;
  var kz#0: bool;
  var $rhs##0: bool;
  var x##0: bool;
  var u##0: Box;
  var $tmp##0: Box;
  var a#0: bool;
  var $rhs##1: bool;
  var $tmp##1: Box;

    // AddMethodImpl: Main, Impl$$_module.C.Main
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(17,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(18,11)
    assume true;
    ##x#0 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, TInt, $Heap);
    ##u#0 := u#0;
    // assume allocatedness for argument to function
    assume $IsAllocBox(##u#0, _module.C$U, $Heap);
    assume _module.C.F#canCall(_module.C$U, TInt, this, $Box(LitInt(3)), u#0);
    if (_module.C.F(_module.C$U, TInt, this, $Box(LitInt(3)), u#0))
    {
        ##x#1 := this;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#1, Tclass._module.C(_module.C$U), $Heap);
        ##u#1 := u#0;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##u#1, _module.C$U, $Heap);
        assume _module.C.F#canCall(_module.C$U, Tclass._module.C(_module.C$U), this, $Box(this), u#0);
    }

    assume _module.C.F#canCall(_module.C$U, TInt, this, $Box(LitInt(3)), u#0)
       && (_module.C.F(_module.C$U, TInt, this, $Box(LitInt(3)), u#0)
         ==> _module.C.F#canCall(_module.C$U, Tclass._module.C(_module.C$U), this, $Box(this), u#0));
    t#0 := _module.C.F(_module.C$U, TInt, this, $Box(LitInt(3)), u#0)
       && _module.C.F(_module.C$U, Tclass._module.C(_module.C$U), this, $Box(this), u#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(18,32)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(19,16)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := t#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    u##0 := u#0;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##0 := Call$$_module.C.M(_module.C$U, TBool, this, $Box(x##0), u##0);
    havoc $rhs##0;
    assume $rhs##0 == $Unbox($tmp##0): bool;
    // TrCallStmt: After ProcessCallStmt
    kz#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(19,20)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(20,15)
    assume true;
    // TrCallStmt: Adding lhs with type bool
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##1 := Call$$_module.C.G(_module.C$U, TBool, this);
    havoc $rhs##1;
    assume $rhs##1 == $Unbox($tmp##1): bool;
    // TrCallStmt: After ProcessCallStmt
    a#0 := $rhs##1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(20,16)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(21,5)
    if (kz#0)
    {
        if (!a#0)
        {
        }
    }

    assume true;
    assert {:subsumption 0} kz#0;
    assert {:subsumption 0} a#0 || !a#0;
    assume kz#0 && (a#0 || !a#0);
}



procedure CheckWellformed$$_module.C.G(_module.C$U: Ty, 
    _module.C.G$Y: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap))
   returns (a#0: Box
       where $IsBox(a#0, _module.C.G$Y) && $IsAllocBox(a#0, _module.C.G$Y, $Heap));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.C.G(_module.C$U: Ty, 
    _module.C.G$Y: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.C(_module.C$U))
         && $IsAlloc(this, Tclass._module.C(_module.C$U), $Heap))
   returns (a#0: Box
       where $IsBox(a#0, _module.C.G$Y) && $IsAllocBox(a#0, _module.C.G$Y, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.C: subset type $Is
axiom (forall _module.C$U: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.C(_module.C$U)) } 
  $Is(c#0, Tclass._module.C(_module.C$U))
     <==> $Is(c#0, Tclass._module.C?(_module.C$U)) && c#0 != null);

// _module.C: subset type $IsAlloc
axiom (forall _module.C$U: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.C(_module.C$U), $h) } 
  $IsAlloc(c#0, Tclass._module.C(_module.C$U), $h)
     <==> $IsAlloc(c#0, Tclass._module.C?(_module.C$U), $h));

const unique class._module.SetTest?: ClassName;

function Tclass._module.SetTest?() : Ty;

const unique Tagclass._module.SetTest?: TyTag;

// Tclass._module.SetTest? Tag
axiom Tag(Tclass._module.SetTest?()) == Tagclass._module.SetTest?
   && TagFamily(Tclass._module.SetTest?()) == tytagFamily$SetTest;

// Box/unbox axiom for Tclass._module.SetTest?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SetTest?()) } 
  $IsBox(bx, Tclass._module.SetTest?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.SetTest?()));

// SetTest: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.SetTest?()) } 
  $Is($o, Tclass._module.SetTest?())
     <==> $o == null || dtype($o) == Tclass._module.SetTest?());

// SetTest: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.SetTest?(), $h) } 
  $IsAlloc($o, Tclass._module.SetTest?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.SetTest() : Ty;

const unique Tagclass._module.SetTest: TyTag;

// Tclass._module.SetTest Tag
axiom Tag(Tclass._module.SetTest()) == Tagclass._module.SetTest
   && TagFamily(Tclass._module.SetTest()) == tytagFamily$SetTest;

// Box/unbox axiom for Tclass._module.SetTest
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SetTest()) } 
  $IsBox(bx, Tclass._module.SetTest())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.SetTest()));

procedure CheckWellformed$$_module.SetTest.Add(_module.SetTest.Add$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(_module.SetTest.Add$T))
         && $IsAlloc(s#0, TSet(_module.SetTest.Add$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.SetTest.Add$T)
         && $IsAllocBox(x#0, _module.SetTest.Add$T, $Heap))
   returns (t#0: Set Box
       where $Is(t#0, TSet(_module.SetTest.Add$T))
         && $IsAlloc(t#0, TSet(_module.SetTest.Add$T), $Heap));
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.SetTest.Add(_module.SetTest.Add$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(_module.SetTest.Add$T))
         && $IsAlloc(s#0, TSet(_module.SetTest.Add$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.SetTest.Add$T)
         && $IsAllocBox(x#0, _module.SetTest.Add$T, $Heap))
   returns (t#0: Set Box
       where $Is(t#0, TSet(_module.SetTest.Add$T))
         && $IsAlloc(t#0, TSet(_module.SetTest.Add$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Set#Equal(t#0, Set#Union(s#0, Set#UnionOne(Set#Empty(): Set Box, x#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SetTest.Add(_module.SetTest.Add$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap), 
    s#0: Set Box
       where $Is(s#0, TSet(_module.SetTest.Add$T))
         && $IsAlloc(s#0, TSet(_module.SetTest.Add$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.SetTest.Add$T)
         && $IsAllocBox(x#0, _module.SetTest.Add$T, $Heap))
   returns (t#0: Set Box
       where $Is(t#0, TSet(_module.SetTest.Add$T))
         && $IsAlloc(t#0, TSet(_module.SetTest.Add$T), $Heap), 
    $_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Set#Equal(t#0, Set#Union(s#0, Set#UnionOne(Set#Empty(): Set Box, x#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SetTest.Add(_module.SetTest.Add$T: Ty, this: ref, s#0: Set Box, x#0: Box)
   returns (t#0: Set Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Add, Impl$$_module.SetTest.Add
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(29,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(30,7)
    assume true;
    assume true;
    t#0 := Set#Union(s#0, Set#UnionOne(Set#Empty(): Set Box, x#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(30,16)"} true;
}



procedure CheckWellformed$$_module.SetTest.Good(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.SetTest.Good(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SetTest.Good(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SetTest.Good(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap);
  var t#0: Set Box where $Is(t#0, TSet(TInt)) && $IsAlloc(t#0, TSet(TInt), $Heap);
  var $rhs##0: Set Box
     where $Is($rhs##0, TSet(TInt)) && $IsAlloc($rhs##0, TSet(TInt), $Heap);
  var s##0: Set Box;
  var x##0: int;

    // AddMethodImpl: Good, Impl$$_module.SetTest.Good
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(34,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(35,11)
    assume true;
    assume true;
    s#0 := Lit(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(2))), $Box(LitInt(5))), 
        $Box(LitInt(3))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(35,22)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(36,17)
    assume true;
    // TrCallStmt: Adding lhs with type set<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(7);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.SetTest.Add(TInt, this, s##0, $Box(x##0));
    // TrCallStmt: After ProcessCallStmt
    t#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(36,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(37,5)
    assume true;
    assert Set#Equal(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(5))), $Box(LitInt(7))), 
          $Box(LitInt(2))), 
        $Box(LitInt(3))), 
      t#0);
}



procedure CheckWellformed$$_module.SetTest.Bad(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap));
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.SetTest.Bad(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SetTest.Bad(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SetTest())
         && $IsAlloc(this, Tclass._module.SetTest(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SetTest.Bad(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Set Box where $Is(s#0, TSet(TInt)) && $IsAlloc(s#0, TSet(TInt), $Heap);
  var t#0: Set Box where $Is(t#0, TSet(TInt)) && $IsAlloc(t#0, TSet(TInt), $Heap);
  var $rhs##0: Set Box
     where $Is($rhs##0, TSet(TInt)) && $IsAlloc($rhs##0, TSet(TInt), $Heap);
  var s##0: Set Box;
  var x##0: int;

    // AddMethodImpl: Bad, Impl$$_module.SetTest.Bad
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(41,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(42,11)
    assume true;
    assume true;
    s#0 := Lit(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(2))), $Box(LitInt(50))), 
        $Box(LitInt(3))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(42,23)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(43,17)
    assume true;
    // TrCallStmt: Adding lhs with type set<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(7);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.SetTest.Add(TInt, this, s##0, $Box(x##0));
    // TrCallStmt: After ProcessCallStmt
    t#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(43,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(44,5)
    assume true;
    assert Set#Equal(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(LitInt(5))), $Box(LitInt(7))), 
          $Box(LitInt(2))), 
        $Box(LitInt(3))), 
      t#0);
}



// _module.SetTest: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.SetTest()) } 
  $Is(c#0, Tclass._module.SetTest())
     <==> $Is(c#0, Tclass._module.SetTest?()) && c#0 != null);

// _module.SetTest: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.SetTest(), $h) } 
  $IsAlloc(c#0, Tclass._module.SetTest(), $h)
     <==> $IsAlloc(c#0, Tclass._module.SetTest?(), $h));

const unique class._module.SequenceTest?: ClassName;

function Tclass._module.SequenceTest?() : Ty;

const unique Tagclass._module.SequenceTest?: TyTag;

// Tclass._module.SequenceTest? Tag
axiom Tag(Tclass._module.SequenceTest?()) == Tagclass._module.SequenceTest?
   && TagFamily(Tclass._module.SequenceTest?()) == tytagFamily$SequenceTest;

// Box/unbox axiom for Tclass._module.SequenceTest?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SequenceTest?()) } 
  $IsBox(bx, Tclass._module.SequenceTest?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.SequenceTest?()));

// SequenceTest: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.SequenceTest?()) } 
  $Is($o, Tclass._module.SequenceTest?())
     <==> $o == null || dtype($o) == Tclass._module.SequenceTest?());

// SequenceTest: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.SequenceTest?(), $h) } 
  $IsAlloc($o, Tclass._module.SequenceTest?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.SequenceTest() : Ty;

const unique Tagclass._module.SequenceTest: TyTag;

// Tclass._module.SequenceTest Tag
axiom Tag(Tclass._module.SequenceTest()) == Tagclass._module.SequenceTest
   && TagFamily(Tclass._module.SequenceTest()) == tytagFamily$SequenceTest;

// Box/unbox axiom for Tclass._module.SequenceTest
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.SequenceTest()) } 
  $IsBox(bx, Tclass._module.SequenceTest())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.SequenceTest()));

procedure CheckWellformed$$_module.SequenceTest.Add(_module.SequenceTest.Add$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap), 
    s#0: Seq Box
       where $Is(s#0, TSeq(_module.SequenceTest.Add$T))
         && $IsAlloc(s#0, TSeq(_module.SequenceTest.Add$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.SequenceTest.Add$T)
         && $IsAllocBox(x#0, _module.SequenceTest.Add$T, $Heap))
   returns (t#0: Seq Box
       where $Is(t#0, TSeq(_module.SequenceTest.Add$T))
         && $IsAlloc(t#0, TSeq(_module.SequenceTest.Add$T), $Heap));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.SequenceTest.Add(_module.SequenceTest.Add$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap), 
    s#0: Seq Box
       where $Is(s#0, TSeq(_module.SequenceTest.Add$T))
         && $IsAlloc(s#0, TSeq(_module.SequenceTest.Add$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.SequenceTest.Add$T)
         && $IsAllocBox(x#0, _module.SequenceTest.Add$T, $Heap))
   returns (t#0: Seq Box
       where $Is(t#0, TSeq(_module.SequenceTest.Add$T))
         && $IsAlloc(t#0, TSeq(_module.SequenceTest.Add$T), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(t#0, Seq#Append(s#0, Seq#Build(Seq#Empty(): Seq Box, x#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SequenceTest.Add(_module.SequenceTest.Add$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap), 
    s#0: Seq Box
       where $Is(s#0, TSeq(_module.SequenceTest.Add$T))
         && $IsAlloc(s#0, TSeq(_module.SequenceTest.Add$T), $Heap), 
    x#0: Box
       where $IsBox(x#0, _module.SequenceTest.Add$T)
         && $IsAllocBox(x#0, _module.SequenceTest.Add$T, $Heap))
   returns (t#0: Seq Box
       where $Is(t#0, TSeq(_module.SequenceTest.Add$T))
         && $IsAlloc(t#0, TSeq(_module.SequenceTest.Add$T), $Heap), 
    $_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures Seq#Equal(t#0, Seq#Append(s#0, Seq#Build(Seq#Empty(): Seq Box, x#0)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SequenceTest.Add(_module.SequenceTest.Add$T: Ty, this: ref, s#0: Seq Box, x#0: Box)
   returns (t#0: Seq Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Add, Impl$$_module.SequenceTest.Add
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(51,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(52,7)
    assume true;
    assume true;
    t#0 := Seq#Append(s#0, Seq#Build(Seq#Empty(): Seq Box, x#0));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(52,16)"} true;
}



procedure CheckWellformed$$_module.SequenceTest.Good(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap));
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.SequenceTest.Good(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SequenceTest.Good(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SequenceTest.Good(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap);
  var t#0: Seq Box where $Is(t#0, TSeq(TInt)) && $IsAlloc(t#0, TSeq(TInt), $Heap);
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var s##0: Seq Box;
  var x##0: int;

    // AddMethodImpl: Good, Impl$$_module.SequenceTest.Good
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(56,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(57,11)
    assume true;
    assume true;
    s#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(2))), $Box(LitInt(5))), 
        $Box(LitInt(3))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(57,22)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(58,17)
    assume true;
    // TrCallStmt: Adding lhs with type seq<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(7);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.SequenceTest.Add(TInt, this, s##0, $Box(x##0));
    // TrCallStmt: After ProcessCallStmt
    t#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(58,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(59,5)
    assume true;
    assert Seq#Equal(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(2))), $Box(LitInt(5))), 
          $Box(LitInt(3))), 
        $Box(LitInt(7))), 
      t#0);
}



procedure CheckWellformed$$_module.SequenceTest.Bad(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.SequenceTest.Bad(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.SequenceTest.Bad(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.SequenceTest())
         && $IsAlloc(this, Tclass._module.SequenceTest(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.SequenceTest.Bad(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#0: Seq Box where $Is(s#0, TSeq(TInt)) && $IsAlloc(s#0, TSeq(TInt), $Heap);
  var t#0: Seq Box where $Is(t#0, TSeq(TInt)) && $IsAlloc(t#0, TSeq(TInt), $Heap);
  var $rhs##0: Seq Box
     where $Is($rhs##0, TSeq(TInt)) && $IsAlloc($rhs##0, TSeq(TInt), $Heap);
  var s##0: Seq Box;
  var x##0: int;

    // AddMethodImpl: Bad, Impl$$_module.SequenceTest.Bad
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(63,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(64,11)
    assume true;
    assume true;
    s#0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(2))), $Box(LitInt(5))), 
        $Box(LitInt(3))));
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(64,22)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(65,17)
    assume true;
    // TrCallStmt: Adding lhs with type seq<int>
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assume true;
    // ProcessCallStmt: CheckSubrange
    s##0 := s#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(7);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.SequenceTest.Add(TInt, this, s##0, $Box(x##0));
    // TrCallStmt: After ProcessCallStmt
    t#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(65,22)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(66,5)
    if (!Seq#Equal(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(2))), $Box(LitInt(5))), 
          $Box(LitInt(7))), 
        $Box(LitInt(3))), 
      t#0))
    {
    }

    assume true;
    assert Seq#Equal(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(2))), $Box(LitInt(5))), 
            $Box(LitInt(7))), 
          $Box(LitInt(3))), 
        t#0)
       || Seq#Equal(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(LitInt(2))), $Box(LitInt(5))), 
          $Box(LitInt(3))), 
        t#0);
}



// _module.SequenceTest: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.SequenceTest()) } 
  $Is(c#0, Tclass._module.SequenceTest())
     <==> $Is(c#0, Tclass._module.SequenceTest?()) && c#0 != null);

// _module.SequenceTest: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.SequenceTest(), $h) } 
  $IsAlloc(c#0, Tclass._module.SequenceTest(), $h)
     <==> $IsAlloc(c#0, Tclass._module.SequenceTest?(), $h));

const unique class._module.CC?: ClassName;

function Tclass._module.CC?(Ty) : Ty;

const unique Tagclass._module.CC?: TyTag;

// Tclass._module.CC? Tag
axiom (forall _module.CC$T: Ty :: 
  { Tclass._module.CC?(_module.CC$T) } 
  Tag(Tclass._module.CC?(_module.CC$T)) == Tagclass._module.CC?
     && TagFamily(Tclass._module.CC?(_module.CC$T)) == tytagFamily$CC);

// Tclass._module.CC? injectivity 0
axiom (forall _module.CC$T: Ty :: 
  { Tclass._module.CC?(_module.CC$T) } 
  Tclass._module.CC?_0(Tclass._module.CC?(_module.CC$T)) == _module.CC$T);

function Tclass._module.CC?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.CC?
axiom (forall _module.CC$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.CC?(_module.CC$T)) } 
  $IsBox(bx, Tclass._module.CC?(_module.CC$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.CC?(_module.CC$T)));

// CC: Class $Is
axiom (forall _module.CC$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.CC?(_module.CC$T)) } 
  $Is($o, Tclass._module.CC?(_module.CC$T))
     <==> $o == null || dtype($o) == Tclass._module.CC?(_module.CC$T));

// CC: Class $IsAlloc
axiom (forall _module.CC$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.CC?(_module.CC$T), $h) } 
  $IsAlloc($o, Tclass._module.CC?(_module.CC$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.CC.x) == 0
   && FieldOfDecl(class._module.CC?, field$x) == _module.CC.x
   && !$IsGhostField(_module.CC.x);

const _module.CC.x: Field Box;

// CC.x: Type axiom
axiom (forall _module.CC$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.CC.x), Tclass._module.CC?(_module.CC$T) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.CC?(_module.CC$T)
     ==> $IsBox(read($h, $o, _module.CC.x), _module.CC$T));

// CC.x: Allocation axiom
axiom (forall _module.CC$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.CC.x), Tclass._module.CC?(_module.CC$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.CC?(_module.CC$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.CC.x), _module.CC$T, $h));

function Tclass._module.CC(Ty) : Ty;

const unique Tagclass._module.CC: TyTag;

// Tclass._module.CC Tag
axiom (forall _module.CC$T: Ty :: 
  { Tclass._module.CC(_module.CC$T) } 
  Tag(Tclass._module.CC(_module.CC$T)) == Tagclass._module.CC
     && TagFamily(Tclass._module.CC(_module.CC$T)) == tytagFamily$CC);

// Tclass._module.CC injectivity 0
axiom (forall _module.CC$T: Ty :: 
  { Tclass._module.CC(_module.CC$T) } 
  Tclass._module.CC_0(Tclass._module.CC(_module.CC$T)) == _module.CC$T);

function Tclass._module.CC_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.CC
axiom (forall _module.CC$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.CC(_module.CC$T)) } 
  $IsBox(bx, Tclass._module.CC(_module.CC$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.CC(_module.CC$T)));

procedure CheckWellformed$$_module.CC.M(_module.CC$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CC(_module.CC$T))
         && $IsAlloc(this, Tclass._module.CC(_module.CC$T), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.CC(_module.CC$T))
         && $IsAlloc(c#0, Tclass._module.CC(_module.CC$T), $Heap), 
    z#0: Box
       where $IsBox(z#0, _module.CC$T) && $IsAllocBox(z#0, _module.CC$T, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module.CC$T) && $IsAllocBox(y#0, _module.CC$T, $Heap));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.CC.M(_module.CC$T: Ty, this: ref, c#0: ref, z#0: Box) returns (y#0: Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M, CheckWellformed$$_module.CC.M
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(75,9): initial state"} true;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == this);
    assume $HeapSucc(old($Heap), $Heap);
    havoc y#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(77,21): post-state"} true;
    assert c#0 != null;
    assume y#0 == read($Heap, c#0, _module.CC.x);
    assume read($Heap, this, _module.CC.x) == z#0;
}



procedure Call$$_module.CC.M(_module.CC$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CC(_module.CC$T))
         && $IsAlloc(this, Tclass._module.CC(_module.CC$T), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.CC(_module.CC$T))
         && $IsAlloc(c#0, Tclass._module.CC(_module.CC$T), $Heap), 
    z#0: Box
       where $IsBox(z#0, _module.CC$T) && $IsAllocBox(z#0, _module.CC$T, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module.CC$T) && $IsAllocBox(y#0, _module.CC$T, $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures y#0 == read($Heap, c#0, _module.CC.x);
  ensures read($Heap, this, _module.CC.x) == z#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.CC.M(_module.CC$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CC(_module.CC$T))
         && $IsAlloc(this, Tclass._module.CC(_module.CC$T), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.CC(_module.CC$T))
         && $IsAlloc(c#0, Tclass._module.CC(_module.CC$T), $Heap), 
    z#0: Box
       where $IsBox(z#0, _module.CC$T) && $IsAllocBox(z#0, _module.CC$T, $Heap))
   returns (y#0: Box
       where $IsBox(y#0, _module.CC$T) && $IsAllocBox(y#0, _module.CC$T, $Heap), 
    $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures y#0 == read($Heap, c#0, _module.CC.x);
  ensures read($Heap, this, _module.CC.x) == z#0;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == this);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.CC.M(_module.CC$T: Ty, this: ref, c#0: ref, z#0: Box)
   returns (y#0: Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $rhs#0: Box where $IsBox($rhs#0, _module.CC$T);
  var $rhs#1: Box where $IsBox($rhs#1, _module.CC$T);

    // AddMethodImpl: M, Impl$$_module.CC.M
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(78,2): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(79,7)
    assume true;
    assert $_Frame[this, _module.CC.x];
    assert c#0 != null;
    assume true;
    $rhs#0 := read($Heap, c#0, _module.CC.x);
    $Heap := update($Heap, this, _module.CC.x, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(79,12)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(80,7)
    assume true;
    assert $_Frame[this, _module.CC.x];
    assume true;
    $rhs#1 := z#0;
    $Heap := update($Heap, this, _module.CC.x, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(80,10)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(81,7)
    assume true;
    assert c#0 != null;
    assume true;
    y#0 := read($Heap, c#0, _module.CC.x);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(81,12)"} true;
}



// _module.CC: subset type $Is
axiom (forall _module.CC$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.CC(_module.CC$T)) } 
  $Is(c#0, Tclass._module.CC(_module.CC$T))
     <==> $Is(c#0, Tclass._module.CC?(_module.CC$T)) && c#0 != null);

// _module.CC: subset type $IsAlloc
axiom (forall _module.CC$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.CC(_module.CC$T), $h) } 
  $IsAlloc(c#0, Tclass._module.CC(_module.CC$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.CC?(_module.CC$T), $h));

const unique class._module.CClient?: ClassName;

function Tclass._module.CClient?() : Ty;

const unique Tagclass._module.CClient?: TyTag;

// Tclass._module.CClient? Tag
axiom Tag(Tclass._module.CClient?()) == Tagclass._module.CClient?
   && TagFamily(Tclass._module.CClient?()) == tytagFamily$CClient;

// Box/unbox axiom for Tclass._module.CClient?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.CClient?()) } 
  $IsBox(bx, Tclass._module.CClient?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.CClient?()));

// CClient: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.CClient?()) } 
  $Is($o, Tclass._module.CClient?())
     <==> $o == null || dtype($o) == Tclass._module.CClient?());

// CClient: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.CClient?(), $h) } 
  $IsAlloc($o, Tclass._module.CClient?(), $h)
     <==> $o == null || read($h, $o, alloc));

function Tclass._module.CClient() : Ty;

const unique Tagclass._module.CClient: TyTag;

// Tclass._module.CClient Tag
axiom Tag(Tclass._module.CClient()) == Tagclass._module.CClient
   && TagFamily(Tclass._module.CClient()) == tytagFamily$CClient;

// Box/unbox axiom for Tclass._module.CClient
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.CClient()) } 
  $IsBox(bx, Tclass._module.CClient())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.CClient()));

procedure CheckWellformed$$_module.CClient.Main(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CClient())
         && $IsAlloc(this, Tclass._module.CClient(), $Heap));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.CClient.Main(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CClient())
         && $IsAlloc(this, Tclass._module.CClient(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.CClient.Main(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.CClient())
         && $IsAlloc(this, Tclass._module.CClient(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.CClient.Main(this: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.CC(TInt))
       && $IsAlloc(c#0, Tclass._module.CC(TInt), $Heap);
  var $nw: ref;
  var k#0: int;
  var m#0: int;
  var $rhs#0: int;
  var $rhs#1: int;
  var z#0: int;
  var $rhs##0: int;
  var c##0: ref;
  var z##0: int;
  var $tmp##0: Box;

    // AddMethodImpl: Main, Impl$$_module.CClient.Main
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(86,16): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(87,11)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.CC?(TInt);
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(87,24)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(88,11)
    assume true;
    assert c#0 != null;
    assume true;
    k#0 := $Unbox(read($Heap, c#0, _module.CC.x)): int + 3;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(88,20)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(89,5)
    assert c#0 != null;
    assert c#0 != null;
    assume true;
    if ($Unbox(read($Heap, c#0, _module.CC.x)): int
       == $Unbox(read($Heap, c#0, _module.CC.x)): int)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(90,9)
        assume true;
        assume true;
        k#0 := k#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(90,16)"} true;
    }
    else
    {
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(92,11)
    assume true;
    assert c#0 != null;
    assume true;
    m#0 := $Unbox(read($Heap, c#0, _module.CC.x)): int;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(92,16)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(93,5)
    assert c#0 != null;
    assume true;
    if (m#0 == $Unbox(read($Heap, c#0, _module.CC.x)): int)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(94,9)
        assume true;
        assume true;
        k#0 := k#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(94,16)"} true;
    }
    else
    {
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(96,9)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, _module.CC.x];
    assume true;
    $rhs#0 := LitInt(5);
    $Heap := update($Heap, c#0, _module.CC.x, $Box($rhs#0));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(96,12)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(97,9)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, _module.CC.x];
    assert c#0 != null;
    assume true;
    $rhs#1 := $Unbox(read($Heap, c#0, _module.CC.x)): int;
    $Heap := update($Heap, c#0, _module.CC.x, $Box($rhs#1));
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(97,14)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(98,17)
    assume true;
    // TrCallStmt: Adding lhs with type int
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert c#0 != null;
    assume true;
    // ProcessCallStmt: CheckSubrange
    c##0 := c#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    z##0 := LitInt(17);
    assert (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) && $o == c#0 ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##0 := Call$$_module.CC.M(TInt, c#0, c##0, $Box(z##0));
    havoc $rhs##0;
    assume $rhs##0 == $Unbox($tmp##0): int;
    // TrCallStmt: After ProcessCallStmt
    z#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(98,23)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(99,5)
    assert {:subsumption 0} c#0 != null;
    assume true;
    assert z#0 == $Unbox(read($Heap, c#0, _module.CC.x)): int;
}



// _module.CClient: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.CClient()) } 
  $Is(c#0, Tclass._module.CClient())
     <==> $Is(c#0, Tclass._module.CClient?()) && c#0 != null);

// _module.CClient: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.CClient(), $h) } 
  $IsAlloc(c#0, Tclass._module.CClient(), $h)
     <==> $IsAlloc(c#0, Tclass._module.CClient?(), $h));

const unique class._module.TyKn__C?: ClassName;

function Tclass._module.TyKn__C?(Ty) : Ty;

const unique Tagclass._module.TyKn__C?: TyTag;

// Tclass._module.TyKn__C? Tag
axiom (forall _module.TyKn_C$T: Ty :: 
  { Tclass._module.TyKn__C?(_module.TyKn_C$T) } 
  Tag(Tclass._module.TyKn__C?(_module.TyKn_C$T)) == Tagclass._module.TyKn__C?
     && TagFamily(Tclass._module.TyKn__C?(_module.TyKn_C$T)) == tytagFamily$TyKn_C);

// Tclass._module.TyKn__C? injectivity 0
axiom (forall _module.TyKn_C$T: Ty :: 
  { Tclass._module.TyKn__C?(_module.TyKn_C$T) } 
  Tclass._module.TyKn__C?_0(Tclass._module.TyKn__C?(_module.TyKn_C$T))
     == _module.TyKn_C$T);

function Tclass._module.TyKn__C?_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.TyKn__C?
axiom (forall _module.TyKn_C$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.TyKn__C?(_module.TyKn_C$T)) } 
  $IsBox(bx, Tclass._module.TyKn__C?(_module.TyKn_C$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.TyKn__C?(_module.TyKn_C$T)));

// TyKn_C: Class $Is
axiom (forall _module.TyKn_C$T: Ty, $o: ref :: 
  { $Is($o, Tclass._module.TyKn__C?(_module.TyKn_C$T)) } 
  $Is($o, Tclass._module.TyKn__C?(_module.TyKn_C$T))
     <==> $o == null || dtype($o) == Tclass._module.TyKn__C?(_module.TyKn_C$T));

// TyKn_C: Class $IsAlloc
axiom (forall _module.TyKn_C$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.TyKn__C?(_module.TyKn_C$T), $h) } 
  $IsAlloc($o, Tclass._module.TyKn__C?(_module.TyKn_C$T), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.TyKn__C.x) == 0
   && FieldOfDecl(class._module.TyKn__C?, field$x) == _module.TyKn__C.x
   && !$IsGhostField(_module.TyKn__C.x);

const _module.TyKn__C.x: Field Box;

// TyKn_C.x: Type axiom
axiom (forall _module.TyKn_C$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.TyKn__C.x), Tclass._module.TyKn__C?(_module.TyKn_C$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.TyKn__C?(_module.TyKn_C$T)
     ==> $IsBox(read($h, $o, _module.TyKn__C.x), _module.TyKn_C$T));

// TyKn_C.x: Allocation axiom
axiom (forall _module.TyKn_C$T: Ty, $h: Heap, $o: ref :: 
  { read($h, $o, _module.TyKn__C.x), Tclass._module.TyKn__C?(_module.TyKn_C$T) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.TyKn__C?(_module.TyKn_C$T)
       && read($h, $o, alloc)
     ==> $IsAllocBox(read($h, $o, _module.TyKn__C.x), _module.TyKn_C$T, $h));

// function declaration for _module.TyKn_C.G
function _module.TyKn__C.G(_module.TyKn_C$T: Ty, $heap: Heap, this: ref) : Box;

function _module.TyKn__C.G#canCall(_module.TyKn_C$T: Ty, $heap: Heap, this: ref) : bool;

function Tclass._module.TyKn__C(Ty) : Ty;

const unique Tagclass._module.TyKn__C: TyTag;

// Tclass._module.TyKn__C Tag
axiom (forall _module.TyKn_C$T: Ty :: 
  { Tclass._module.TyKn__C(_module.TyKn_C$T) } 
  Tag(Tclass._module.TyKn__C(_module.TyKn_C$T)) == Tagclass._module.TyKn__C
     && TagFamily(Tclass._module.TyKn__C(_module.TyKn_C$T)) == tytagFamily$TyKn_C);

// Tclass._module.TyKn__C injectivity 0
axiom (forall _module.TyKn_C$T: Ty :: 
  { Tclass._module.TyKn__C(_module.TyKn_C$T) } 
  Tclass._module.TyKn__C_0(Tclass._module.TyKn__C(_module.TyKn_C$T))
     == _module.TyKn_C$T);

function Tclass._module.TyKn__C_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.TyKn__C
axiom (forall _module.TyKn_C$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.TyKn__C(_module.TyKn_C$T)) } 
  $IsBox(bx, Tclass._module.TyKn__C(_module.TyKn_C$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass._module.TyKn__C(_module.TyKn_C$T)));

// frame axiom for _module.TyKn__C.G
axiom (forall _module.TyKn_C$T: Ty, $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.TyKn__C.G(_module.TyKn_C$T, $h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.TyKn__C(_module.TyKn_C$T))
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.TyKn__C.G(_module.TyKn_C$T, $h0, this)
       == _module.TyKn__C.G(_module.TyKn_C$T, $h1, this));

// consequence axiom for _module.TyKn__C.G
axiom 37 <= $FunctionContextHeight
   ==> (forall _module.TyKn_C$T: Ty, $Heap: Heap, this: ref :: 
    { _module.TyKn__C.G(_module.TyKn_C$T, $Heap, this) } 
    _module.TyKn__C.G#canCall(_module.TyKn_C$T, $Heap, this)
         || (37 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TyKn__C(_module.TyKn_C$T))
           && $IsAlloc(this, Tclass._module.TyKn__C(_module.TyKn_C$T), $Heap))
       ==> $IsBox(_module.TyKn__C.G(_module.TyKn_C$T, $Heap, this), _module.TyKn_C$T));

function _module.TyKn__C.G#requires(Ty, Heap, ref) : bool;

// #requires axiom for _module.TyKn__C.G
axiom (forall _module.TyKn_C$T: Ty, $Heap: Heap, this: ref :: 
  { _module.TyKn__C.G#requires(_module.TyKn_C$T, $Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.TyKn__C(_module.TyKn_C$T))
       && $IsAlloc(this, Tclass._module.TyKn__C(_module.TyKn_C$T), $Heap)
     ==> _module.TyKn__C.G#requires(_module.TyKn_C$T, $Heap, this) == true);

// definition axiom for _module.TyKn__C.G (revealed)
axiom 37 <= $FunctionContextHeight
   ==> (forall _module.TyKn_C$T: Ty, $Heap: Heap, this: ref :: 
    { _module.TyKn__C.G(_module.TyKn_C$T, $Heap, this), $IsGoodHeap($Heap) } 
    _module.TyKn__C.G#canCall(_module.TyKn_C$T, $Heap, this)
         || (37 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.TyKn__C(_module.TyKn_C$T))
           && $IsAlloc(this, Tclass._module.TyKn__C(_module.TyKn_C$T), $Heap))
       ==> _module.TyKn__C.G(_module.TyKn_C$T, $Heap, this)
         == read($Heap, this, _module.TyKn__C.x));

procedure CheckWellformed$$_module.TyKn__C.G(_module.TyKn_C$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TyKn__C(_module.TyKn_C$T))
         && $IsAlloc(this, Tclass._module.TyKn__C(_module.TyKn_C$T), $Heap));
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.TyKn__C.G(_module.TyKn_C$T: Ty, this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function G
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(185,11): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    if (*)
    {
        assume $IsBox(_module.TyKn__C.G(_module.TyKn_C$T, $Heap, this), _module.TyKn_C$T);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> $o == this);
        b$reqreads#0 := $_Frame[this, _module.TyKn__C.x];
        assume _module.TyKn__C.G(_module.TyKn_C$T, $Heap, this)
           == read($Heap, this, _module.TyKn__C.x);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $IsBox(_module.TyKn__C.G(_module.TyKn_C$T, $Heap, this), _module.TyKn_C$T);
        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.TyKn__C.M(_module.TyKn_C$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TyKn__C(_module.TyKn_C$T))
         && $IsAlloc(this, Tclass._module.TyKn__C(_module.TyKn_C$T), $Heap))
   returns (t#0: Box
       where $IsBox(t#0, _module.TyKn_C$T) && $IsAllocBox(t#0, _module.TyKn_C$T, $Heap));
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.TyKn__C.M(_module.TyKn_C$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TyKn__C(_module.TyKn_C$T))
         && $IsAlloc(this, Tclass._module.TyKn__C(_module.TyKn_C$T), $Heap))
   returns (t#0: Box
       where $IsBox(t#0, _module.TyKn_C$T) && $IsAllocBox(t#0, _module.TyKn_C$T, $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.TyKn__C.M(_module.TyKn_C$T: Ty, 
    this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TyKn__C(_module.TyKn_C$T))
         && $IsAlloc(this, Tclass._module.TyKn__C(_module.TyKn_C$T), $Heap))
   returns (t#0: Box
       where $IsBox(t#0, _module.TyKn_C$T) && $IsAllocBox(t#0, _module.TyKn_C$T, $Heap), 
    $_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.TyKn_C: subset type $Is
axiom (forall _module.TyKn_C$T: Ty, c#0: ref :: 
  { $Is(c#0, Tclass._module.TyKn__C(_module.TyKn_C$T)) } 
  $Is(c#0, Tclass._module.TyKn__C(_module.TyKn_C$T))
     <==> $Is(c#0, Tclass._module.TyKn__C?(_module.TyKn_C$T)) && c#0 != null);

// _module.TyKn_C: subset type $IsAlloc
axiom (forall _module.TyKn_C$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.TyKn__C(_module.TyKn_C$T), $h) } 
  $IsAlloc(c#0, Tclass._module.TyKn__C(_module.TyKn_C$T), $h)
     <==> $IsAlloc(c#0, Tclass._module.TyKn__C?(_module.TyKn_C$T), $h));

const unique class._module.TyKn__K?: ClassName;

function Tclass._module.TyKn__K?() : Ty;

const unique Tagclass._module.TyKn__K?: TyTag;

// Tclass._module.TyKn__K? Tag
axiom Tag(Tclass._module.TyKn__K?()) == Tagclass._module.TyKn__K?
   && TagFamily(Tclass._module.TyKn__K?()) == tytagFamily$TyKn_K;

// Box/unbox axiom for Tclass._module.TyKn__K?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.TyKn__K?()) } 
  $IsBox(bx, Tclass._module.TyKn__K?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.TyKn__K?()));

// TyKn_K: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.TyKn__K?()) } 
  $Is($o, Tclass._module.TyKn__K?())
     <==> $o == null || dtype($o) == Tclass._module.TyKn__K?());

// TyKn_K: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.TyKn__K?(), $h) } 
  $IsAlloc($o, Tclass._module.TyKn__K?(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for _module.TyKn_K.F
function _module.TyKn__K.F(this: ref) : int;

function _module.TyKn__K.F#canCall(this: ref) : bool;

function Tclass._module.TyKn__K() : Ty;

const unique Tagclass._module.TyKn__K: TyTag;

// Tclass._module.TyKn__K Tag
axiom Tag(Tclass._module.TyKn__K()) == Tagclass._module.TyKn__K
   && TagFamily(Tclass._module.TyKn__K()) == tytagFamily$TyKn_K;

// Box/unbox axiom for Tclass._module.TyKn__K
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.TyKn__K()) } 
  $IsBox(bx, Tclass._module.TyKn__K())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.TyKn__K()));

// consequence axiom for _module.TyKn__K.F
axiom 36 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    { _module.TyKn__K.F(this) } 
    _module.TyKn__K.F#canCall(this)
         || (36 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.TyKn__K()))
       ==> true);

function _module.TyKn__K.F#requires(ref) : bool;

// #requires axiom for _module.TyKn__K.F
axiom (forall this: ref :: 
  { _module.TyKn__K.F#requires(this) } 
  this != null && $Is(this, Tclass._module.TyKn__K())
     ==> _module.TyKn__K.F#requires(this) == true);

// definition axiom for _module.TyKn__K.F (revealed)
axiom 36 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    { _module.TyKn__K.F(this) } 
    _module.TyKn__K.F#canCall(this)
         || (36 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.TyKn__K()))
       ==> _module.TyKn__K.F(this) == LitInt(176));

// definition axiom for _module.TyKn__K.F for all literals (revealed)
axiom 36 <= $FunctionContextHeight
   ==> (forall this: ref :: 
    {:weight 3} { _module.TyKn__K.F(Lit(this)) } 
    _module.TyKn__K.F#canCall(Lit(this))
         || (36 != $FunctionContextHeight
           && 
          this != null
           && $Is(this, Tclass._module.TyKn__K()))
       ==> _module.TyKn__K.F(Lit(this)) == LitInt(176));

procedure CheckWellformed$$_module.TyKn__K.F(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.TyKn__K())
         && $IsAlloc(this, Tclass._module.TyKn__K(), $Heap));
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// _module.TyKn_K: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.TyKn__K()) } 
  $Is(c#0, Tclass._module.TyKn__K())
     <==> $Is(c#0, Tclass._module.TyKn__K?()) && c#0 != null);

// _module.TyKn_K: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.TyKn__K(), $h) } 
  $IsAlloc(c#0, Tclass._module.TyKn__K(), $h)
     <==> $IsAlloc(c#0, Tclass._module.TyKn__K?(), $h));

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
axiom (forall _module.List$T: Ty :: 
  { Tclass._module.List(_module.List$T) } 
  Tag(Tclass._module.List(_module.List$T)) == Tagclass._module.List
     && TagFamily(Tclass._module.List(_module.List$T)) == tytagFamily$List);

// Tclass._module.List injectivity 0
axiom (forall _module.List$T: Ty :: 
  { Tclass._module.List(_module.List$T) } 
  Tclass._module.List_0(Tclass._module.List(_module.List$T)) == _module.List$T);

function Tclass._module.List_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.List
axiom (forall _module.List$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.List(_module.List$T)) } 
  $IsBox(bx, Tclass._module.List(_module.List$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.List(_module.List$T)));

// Constructor $Is
axiom (forall _module.List$T: Ty :: 
  { $Is(#_module.List.Nil(), Tclass._module.List(_module.List$T)) } 
  $Is(#_module.List.Nil(), Tclass._module.List(_module.List$T)));

// Constructor $IsAlloc
axiom (forall _module.List$T: Ty, $h: Heap :: 
  { $IsAlloc(#_module.List.Nil(), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.List.Nil(), Tclass._module.List(_module.List$T), $h));

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
axiom (forall _module.List$T: Ty, a#7#0#0: Box, a#7#1#0: DatatypeType :: 
  { $Is(#_module.List.Cons(a#7#0#0, a#7#1#0), Tclass._module.List(_module.List$T)) } 
  $Is(#_module.List.Cons(a#7#0#0, a#7#1#0), Tclass._module.List(_module.List$T))
     <==> $IsBox(a#7#0#0, _module.List$T)
       && $Is(a#7#1#0, Tclass._module.List(_module.List$T)));

// Constructor $IsAlloc
axiom (forall _module.List$T: Ty, a#8#0#0: Box, a#8#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.List.Cons(a#8#0#0, a#8#1#0), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.List.Cons(a#8#0#0, a#8#1#0), Tclass._module.List(_module.List$T), $h)
       <==> $IsAllocBox(a#8#0#0, _module.List$T, $h)
         && $IsAlloc(a#8#1#0, Tclass._module.List(_module.List$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.List._h1(d), _module.List$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAllocBox(_module.List._h1(d), _module.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAlloc(_module.List._h2(d), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.Cons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAlloc(_module.List._h2(d), Tclass._module.List(_module.List$T), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType :: 
  { #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #_module.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#_module.List.Cons(a#9#0#0, a#9#1#0)));

function _module.List._h1(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType :: 
  { #_module.List.Cons(a#10#0#0, a#10#1#0) } 
  _module.List._h1(#_module.List.Cons(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType :: 
  { #_module.List.Cons(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#_module.List.Cons(a#11#0#0, a#11#1#0)));

function _module.List._h2(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType :: 
  { #_module.List.Cons(a#12#0#0, a#12#1#0) } 
  _module.List._h2(#_module.List.Cons(a#12#0#0, a#12#1#0)) == a#12#1#0);

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
axiom (forall _module.List$T: Ty, d: DatatypeType :: 
  { _module.List.Cons_q(d), $Is(d, Tclass._module.List(_module.List$T)) } 
    { _module.List.Nil_q(d), $Is(d, Tclass._module.List(_module.List$T)) } 
  $Is(d, Tclass._module.List(_module.List$T))
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
       <==> _module.List._h1(a) == _module.List._h1(b)
         && _module.List#Equal(_module.List._h2(a), _module.List._h2(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

// Constructor function declaration
function #_module.Pair.MkPair(Box, Box) : DatatypeType;

const unique ##_module.Pair.MkPair: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box, a#14#1#0: Box :: 
  { #_module.Pair.MkPair(a#14#0#0, a#14#1#0) } 
  DatatypeCtorId(#_module.Pair.MkPair(a#14#0#0, a#14#1#0))
     == ##_module.Pair.MkPair);

function _module.Pair.MkPair_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Pair.MkPair_q(d) } 
  _module.Pair.MkPair_q(d) <==> DatatypeCtorId(d) == ##_module.Pair.MkPair);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Pair.MkPair_q(d) } 
  _module.Pair.MkPair_q(d)
     ==> (exists a#15#0#0: Box, a#15#1#0: Box :: 
      d == #_module.Pair.MkPair(a#15#0#0, a#15#1#0)));

function Tclass._module.Pair(Ty, Ty) : Ty;

const unique Tagclass._module.Pair: TyTag;

// Tclass._module.Pair Tag
axiom (forall _module.Pair$T: Ty, _module.Pair$U: Ty :: 
  { Tclass._module.Pair(_module.Pair$T, _module.Pair$U) } 
  Tag(Tclass._module.Pair(_module.Pair$T, _module.Pair$U))
       == Tagclass._module.Pair
     && TagFamily(Tclass._module.Pair(_module.Pair$T, _module.Pair$U))
       == tytagFamily$Pair);

// Tclass._module.Pair injectivity 0
axiom (forall _module.Pair$T: Ty, _module.Pair$U: Ty :: 
  { Tclass._module.Pair(_module.Pair$T, _module.Pair$U) } 
  Tclass._module.Pair_0(Tclass._module.Pair(_module.Pair$T, _module.Pair$U))
     == _module.Pair$T);

function Tclass._module.Pair_0(Ty) : Ty;

// Tclass._module.Pair injectivity 1
axiom (forall _module.Pair$T: Ty, _module.Pair$U: Ty :: 
  { Tclass._module.Pair(_module.Pair$T, _module.Pair$U) } 
  Tclass._module.Pair_1(Tclass._module.Pair(_module.Pair$T, _module.Pair$U))
     == _module.Pair$U);

function Tclass._module.Pair_1(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Pair
axiom (forall _module.Pair$T: Ty, _module.Pair$U: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Pair(_module.Pair$T, _module.Pair$U)) } 
  $IsBox(bx, Tclass._module.Pair(_module.Pair$T, _module.Pair$U))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Pair(_module.Pair$T, _module.Pair$U)));

// Constructor $Is
axiom (forall _module.Pair$T: Ty, _module.Pair$U: Ty, a#16#0#0: Box, a#16#1#0: Box :: 
  { $Is(#_module.Pair.MkPair(a#16#0#0, a#16#1#0), 
      Tclass._module.Pair(_module.Pair$T, _module.Pair$U)) } 
  $Is(#_module.Pair.MkPair(a#16#0#0, a#16#1#0), 
      Tclass._module.Pair(_module.Pair$T, _module.Pair$U))
     <==> $IsBox(a#16#0#0, _module.Pair$T) && $IsBox(a#16#1#0, _module.Pair$U));

// Constructor $IsAlloc
axiom (forall _module.Pair$T: Ty, _module.Pair$U: Ty, a#17#0#0: Box, a#17#1#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Pair.MkPair(a#17#0#0, a#17#1#0), 
      Tclass._module.Pair(_module.Pair$T, _module.Pair$U), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Pair.MkPair(a#17#0#0, a#17#1#0), 
        Tclass._module.Pair(_module.Pair$T, _module.Pair$U), 
        $h)
       <==> $IsAllocBox(a#17#0#0, _module.Pair$T, $h)
         && $IsAllocBox(a#17#1#0, _module.Pair$U, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Pair$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Pair._0(d), _module.Pair$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Pair.MkPair_q(d)
       && (exists _module.Pair$U: Ty :: 
        { $IsAlloc(d, Tclass._module.Pair(_module.Pair$T, _module.Pair$U), $h) } 
        $IsAlloc(d, Tclass._module.Pair(_module.Pair$T, _module.Pair$U), $h))
     ==> $IsAllocBox(_module.Pair._0(d), _module.Pair$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Pair$U: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Pair._1(d), _module.Pair$U, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Pair.MkPair_q(d)
       && (exists _module.Pair$T: Ty :: 
        { $IsAlloc(d, Tclass._module.Pair(_module.Pair$T, _module.Pair$U), $h) } 
        $IsAlloc(d, Tclass._module.Pair(_module.Pair$T, _module.Pair$U), $h))
     ==> $IsAllocBox(_module.Pair._1(d), _module.Pair$U, $h));

// Constructor literal
axiom (forall a#18#0#0: Box, a#18#1#0: Box :: 
  { #_module.Pair.MkPair(Lit(a#18#0#0), Lit(a#18#1#0)) } 
  #_module.Pair.MkPair(Lit(a#18#0#0), Lit(a#18#1#0))
     == Lit(#_module.Pair.MkPair(a#18#0#0, a#18#1#0)));

function _module.Pair._0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#19#0#0: Box, a#19#1#0: Box :: 
  { #_module.Pair.MkPair(a#19#0#0, a#19#1#0) } 
  _module.Pair._0(#_module.Pair.MkPair(a#19#0#0, a#19#1#0)) == a#19#0#0);

// Inductive rank
axiom (forall a#20#0#0: Box, a#20#1#0: Box :: 
  { #_module.Pair.MkPair(a#20#0#0, a#20#1#0) } 
  BoxRank(a#20#0#0) < DtRank(#_module.Pair.MkPair(a#20#0#0, a#20#1#0)));

function _module.Pair._1(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#21#0#0: Box, a#21#1#0: Box :: 
  { #_module.Pair.MkPair(a#21#0#0, a#21#1#0) } 
  _module.Pair._1(#_module.Pair.MkPair(a#21#0#0, a#21#1#0)) == a#21#1#0);

// Inductive rank
axiom (forall a#22#0#0: Box, a#22#1#0: Box :: 
  { #_module.Pair.MkPair(a#22#0#0, a#22#1#0) } 
  BoxRank(a#22#1#0) < DtRank(#_module.Pair.MkPair(a#22#0#0, a#22#1#0)));

// Depth-one case-split function
function $IsA#_module.Pair(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Pair(d) } 
  $IsA#_module.Pair(d) ==> _module.Pair.MkPair_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Pair$T: Ty, _module.Pair$U: Ty, d: DatatypeType :: 
  { _module.Pair.MkPair_q(d), $Is(d, Tclass._module.Pair(_module.Pair$T, _module.Pair$U)) } 
  $Is(d, Tclass._module.Pair(_module.Pair$T, _module.Pair$U))
     ==> _module.Pair.MkPair_q(d));

// Datatype extensional equality declaration
function _module.Pair#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Pair.MkPair
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Pair#Equal(a, b) } 
  true
     ==> (_module.Pair#Equal(a, b)
       <==> _module.Pair._0(a) == _module.Pair._0(b)
         && _module.Pair._1(a) == _module.Pair._1(b)));

// Datatype extensionality axiom: _module.Pair
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Pair#Equal(a, b) } 
  _module.Pair#Equal(a, b) <==> a == b);

const unique class._module.Pair: ClassName;

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

// function declaration for _module._default.IsCelebrity
function _module.__default.IsCelebrity(_module._default.IsCelebrity$Person: Ty, c#0: Box, people#0: Set Box) : bool;

function _module.__default.IsCelebrity#canCall(_module._default.IsCelebrity$Person: Ty, c#0: Box, people#0: Set Box) : bool;

// consequence axiom for _module.__default.IsCelebrity
axiom 26 <= $FunctionContextHeight
   ==> (forall _module._default.IsCelebrity$Person: Ty, c#0: Box, people#0: Set Box :: 
    { _module.__default.IsCelebrity(_module._default.IsCelebrity$Person, c#0, people#0) } 
    _module.__default.IsCelebrity#canCall(_module._default.IsCelebrity$Person, c#0, people#0)
         || (26 != $FunctionContextHeight
           && 
          $IsBox(c#0, _module._default.IsCelebrity$Person)
           && $Is(people#0, TSet(_module._default.IsCelebrity$Person))
           && (c#0 == c#0 || people#0[c#0]))
       ==> true);

function _module.__default.IsCelebrity#requires(Ty, Box, Set Box) : bool;

// #requires axiom for _module.__default.IsCelebrity
axiom (forall _module._default.IsCelebrity$Person: Ty, c#0: Box, people#0: Set Box :: 
  { _module.__default.IsCelebrity#requires(_module._default.IsCelebrity$Person, c#0, people#0) } 
  $IsBox(c#0, _module._default.IsCelebrity$Person)
       && $Is(people#0, TSet(_module._default.IsCelebrity$Person))
     ==> _module.__default.IsCelebrity#requires(_module._default.IsCelebrity$Person, c#0, people#0)
       == (c#0 == c#0 || people#0[c#0]));

// definition axiom for _module.__default.IsCelebrity (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall _module._default.IsCelebrity$Person: Ty, c#0: Box, people#0: Set Box :: 
    { _module.__default.IsCelebrity(_module._default.IsCelebrity$Person, c#0, people#0) } 
    _module.__default.IsCelebrity#canCall(_module._default.IsCelebrity$Person, c#0, people#0)
         || (26 != $FunctionContextHeight
           && 
          $IsBox(c#0, _module._default.IsCelebrity$Person)
           && $Is(people#0, TSet(_module._default.IsCelebrity$Person))
           && (c#0 == c#0 || people#0[c#0]))
       ==> _module.__default.IsCelebrity(_module._default.IsCelebrity$Person, c#0, people#0)
         == Lit(false));

// definition axiom for _module.__default.IsCelebrity for decreasing-related literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall _module._default.IsCelebrity$Person: Ty, c#0: Box, people#0: Set Box :: 
    {:weight 3} { _module.__default.IsCelebrity(_module._default.IsCelebrity$Person, c#0, Lit(people#0)) } 
    _module.__default.IsCelebrity#canCall(_module._default.IsCelebrity$Person, c#0, Lit(people#0))
         || (26 != $FunctionContextHeight
           && 
          $IsBox(c#0, _module._default.IsCelebrity$Person)
           && $Is(people#0, TSet(_module._default.IsCelebrity$Person))
           && (c#0 == c#0 || Lit(people#0)[c#0]))
       ==> _module.__default.IsCelebrity(_module._default.IsCelebrity$Person, c#0, Lit(people#0))
         == Lit(false));

// definition axiom for _module.__default.IsCelebrity for all literals (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall _module._default.IsCelebrity$Person: Ty, c#0: Box, people#0: Set Box :: 
    {:weight 3} { _module.__default.IsCelebrity(_module._default.IsCelebrity$Person, Lit(c#0), Lit(people#0)) } 
    _module.__default.IsCelebrity#canCall(_module._default.IsCelebrity$Person, Lit(c#0), Lit(people#0))
         || (26 != $FunctionContextHeight
           && 
          $IsBox(c#0, _module._default.IsCelebrity$Person)
           && $Is(people#0, TSet(_module._default.IsCelebrity$Person))
           && (Lit(c#0) == Lit(c#0) || Lit(people#0)[Lit(c#0)]))
       ==> _module.__default.IsCelebrity(_module._default.IsCelebrity$Person, Lit(c#0), Lit(people#0))
         == Lit(false));

procedure CheckWellformed$$_module.__default.IsCelebrity(_module._default.IsCelebrity$Person: Ty, 
    c#0: Box where $IsBox(c#0, _module._default.IsCelebrity$Person), 
    people#0: Set Box where $Is(people#0, TSet(_module._default.IsCelebrity$Person)));
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.FindCelebrity3(people#0: Set Box
       where $Is(people#0, TSet(TInt)) && $IsAlloc(people#0, TSet(TInt), $Heap), 
    c#0: int);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.FindCelebrity3(people#0: Set Box, c#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: int;
  var ##people#0: Set Box;

    // AddMethodImpl: FindCelebrity3, CheckWellformed$$_module.__default.FindCelebrity3
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(111,7): initial state"} true;
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, TInt, $Heap);
    ##people#0 := people#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##people#0, TSet(TInt), $Heap);
    assert {:subsumption 0} ##c#0 == ##c#0 || ##people#0[$Box(##c#0)];
    assume ##c#0 == ##c#0 || ##people#0[$Box(##c#0)];
    assume _module.__default.IsCelebrity#canCall(TInt, $Box(c#0), people#0);
    assume _module.__default.IsCelebrity(TInt, $Box(c#0), people#0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.FindCelebrity3(people#0: Set Box
       where $Is(people#0, TSet(TInt)) && $IsAlloc(people#0, TSet(TInt), $Heap), 
    c#0: int);
  // user-defined preconditions
  requires _module.__default.IsCelebrity#canCall(TInt, $Box(c#0), people#0)
     ==> _module.__default.IsCelebrity(TInt, $Box(c#0), people#0) || Lit(false);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.FindCelebrity3(people#0: Set Box
       where $Is(people#0, TSet(TInt)) && $IsAlloc(people#0, TSet(TInt), $Heap), 
    c#0: int)
   returns ($_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.IsCelebrity#canCall(TInt, $Box(c#0), people#0)
     && 
    _module.__default.IsCelebrity(TInt, $Box(c#0), people#0)
     && Lit(false);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.FindCelebrity3(people#0: Set Box, c#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b#0: bool;
  var ##c#1: int;
  var ##people#1: Set Box;
  var ##c#2: int;
  var ##people#2: Set Box;

    // AddMethodImpl: FindCelebrity3, Impl$$_module.__default.FindCelebrity3
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(113,0): initial state"} true;
    $_reverifyPost := false;
    havoc b#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(115,5)
    assume true;
    ##c#1 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#1, TInt, $Heap);
    ##people#1 := people#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##people#1, TSet(TInt), $Heap);
    assert {:subsumption 0} ##c#1 == ##c#1 || ##people#1[$Box(##c#1)];
    assume ##c#1 == ##c#1 || ##people#1[$Box(##c#1)];
    assume _module.__default.IsCelebrity#canCall(TInt, $Box(c#0), people#0);
    assume _module.__default.IsCelebrity#canCall(TInt, $Box(c#0), people#0);
    b#0 := _module.__default.IsCelebrity(TInt, $Box(c#0), people#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(115,29)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(116,5)
    assume true;
    ##c#2 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#2, TInt, $Heap);
    ##people#2 := people#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##people#2, TSet(TInt), $Heap);
    assert {:subsumption 0} _module.__default.IsCelebrity#canCall(TInt, $Box(##c#2), ##people#2)
       ==> _module.__default.IsCelebrity(TInt, $Box(##c#2), ##people#2) || Lit(false);
    assume _module.__default.IsCelebrity(TInt, $Box(##c#2), ##people#2);
    assume _module.__default.F#canCall(c#0, people#0);
    assume _module.__default.F#canCall(c#0, people#0);
    b#0 := _module.__default.F(c#0, people#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(116,19)"} true;
}



// function declaration for _module._default.F
function _module.__default.F(c#0: int, people#0: Set Box) : bool;

function _module.__default.F#canCall(c#0: int, people#0: Set Box) : bool;

// consequence axiom for _module.__default.F
axiom 27 <= $FunctionContextHeight
   ==> (forall c#0: int, people#0: Set Box :: 
    { _module.__default.F(c#0, people#0) } 
    _module.__default.F#canCall(c#0, people#0)
         || (27 != $FunctionContextHeight
           && 
          $Is(people#0, TSet(TInt))
           && _module.__default.IsCelebrity(TInt, $Box(c#0), people#0))
       ==> true);

function _module.__default.F#requires(int, Set Box) : bool;

// #requires axiom for _module.__default.F
axiom (forall c#0: int, people#0: Set Box :: 
  { _module.__default.F#requires(c#0, people#0) } 
  $Is(people#0, TSet(TInt))
     ==> _module.__default.F#requires(c#0, people#0)
       == _module.__default.IsCelebrity(TInt, $Box(c#0), people#0));

// definition axiom for _module.__default.F (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall c#0: int, people#0: Set Box :: 
    { _module.__default.F(c#0, people#0) } 
    _module.__default.F#canCall(c#0, people#0)
         || (27 != $FunctionContextHeight
           && 
          $Is(people#0, TSet(TInt))
           && _module.__default.IsCelebrity(TInt, $Box(c#0), people#0))
       ==> _module.__default.F(c#0, people#0) == Lit(false));

// definition axiom for _module.__default.F for all literals (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall c#0: int, people#0: Set Box :: 
    {:weight 3} { _module.__default.F(LitInt(c#0), Lit(people#0)) } 
    _module.__default.F#canCall(LitInt(c#0), Lit(people#0))
         || (27 != $FunctionContextHeight
           && 
          $Is(people#0, TSet(TInt))
           && Lit(_module.__default.IsCelebrity(TInt, $Box(LitInt(c#0)), Lit(people#0))))
       ==> _module.__default.F(LitInt(c#0), Lit(people#0)) == Lit(false));

procedure CheckWellformed$$_module.__default.F(c#0: int, people#0: Set Box where $Is(people#0, TSet(TInt)));
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.F(c#0: int, people#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##c#0: int;
  var ##people#0: Set Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function F
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(119,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    ##c#0 := c#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##c#0, TInt, $Heap);
    ##people#0 := people#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##people#0, TSet(TInt), $Heap);
    assert {:subsumption 0} ##c#0 == ##c#0 || ##people#0[$Box(##c#0)];
    assume ##c#0 == ##c#0 || ##people#0[$Box(##c#0)];
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume _module.__default.IsCelebrity#canCall(TInt, $Box(c#0), people#0);
    assume _module.__default.IsCelebrity(TInt, $Box(c#0), people#0);
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.__default.F(c#0, people#0) == Lit(false);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.F(c#0, people#0), TBool);
    }
}



// function declaration for _module._default.RogerThat
function _module.__default.RogerThat(_module._default.RogerThat$G: Ty, g#0: Box) : Box;

function _module.__default.RogerThat#canCall(_module._default.RogerThat$G: Ty, g#0: Box) : bool;

// consequence axiom for _module.__default.RogerThat
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.RogerThat$G: Ty, g#0: Box :: 
    { _module.__default.RogerThat(_module._default.RogerThat$G, g#0) } 
    _module.__default.RogerThat#canCall(_module._default.RogerThat$G, g#0)
         || (29 != $FunctionContextHeight && $IsBox(g#0, _module._default.RogerThat$G))
       ==> $IsBox(_module.__default.RogerThat(_module._default.RogerThat$G, g#0), 
        _module._default.RogerThat$G));

function _module.__default.RogerThat#requires(Ty, Box) : bool;

// #requires axiom for _module.__default.RogerThat
axiom (forall _module._default.RogerThat$G: Ty, g#0: Box :: 
  { _module.__default.RogerThat#requires(_module._default.RogerThat$G, g#0) } 
  $IsBox(g#0, _module._default.RogerThat$G)
     ==> _module.__default.RogerThat#requires(_module._default.RogerThat$G, g#0) == true);

// definition axiom for _module.__default.RogerThat (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.RogerThat$G: Ty, g#0: Box :: 
    { _module.__default.RogerThat(_module._default.RogerThat$G, g#0) } 
    _module.__default.RogerThat#canCall(_module._default.RogerThat$G, g#0)
         || (29 != $FunctionContextHeight && $IsBox(g#0, _module._default.RogerThat$G))
       ==> _module.__default.RogerThat(_module._default.RogerThat$G, g#0) == g#0);

// definition axiom for _module.__default.RogerThat for all literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.RogerThat$G: Ty, g#0: Box :: 
    {:weight 3} { _module.__default.RogerThat(_module._default.RogerThat$G, Lit(g#0)) } 
    _module.__default.RogerThat#canCall(_module._default.RogerThat$G, Lit(g#0))
         || (29 != $FunctionContextHeight && $IsBox(g#0, _module._default.RogerThat$G))
       ==> _module.__default.RogerThat(_module._default.RogerThat$G, Lit(g#0)) == Lit(g#0));

procedure CheckWellformed$$_module.__default.RogerThat(_module._default.RogerThat$G: Ty, 
    g#0: Box where $IsBox(g#0, _module._default.RogerThat$G));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.Cool
function _module.__default.Cool(b#0: bool) : bool;

function _module.__default.Cool#canCall(b#0: bool) : bool;

// consequence axiom for _module.__default.Cool
axiom 31 <= $FunctionContextHeight
   ==> (forall b#0: bool :: 
    { _module.__default.Cool(b#0) } 
    _module.__default.Cool#canCall(b#0) || 31 != $FunctionContextHeight ==> true);

function _module.__default.Cool#requires(bool) : bool;

// #requires axiom for _module.__default.Cool
axiom (forall b#0: bool :: 
  { _module.__default.Cool#requires(b#0) } 
  _module.__default.Cool#requires(b#0) == true);

// definition axiom for _module.__default.Cool (revealed)
axiom 31 <= $FunctionContextHeight
   ==> (forall b#0: bool :: 
    { _module.__default.Cool(b#0) } 
    _module.__default.Cool#canCall(b#0) || 31 != $FunctionContextHeight
       ==> _module.__default.Cool(b#0) == b#0);

// definition axiom for _module.__default.Cool for all literals (revealed)
axiom 31 <= $FunctionContextHeight
   ==> (forall b#0: bool :: 
    {:weight 3} { _module.__default.Cool(Lit(b#0)) } 
    _module.__default.Cool#canCall(Lit(b#0)) || 31 != $FunctionContextHeight
       ==> _module.__default.Cool(Lit(b#0)) == Lit(b#0));

procedure CheckWellformed$$_module.__default.Cool(b#0: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.Rockin'
function _module.__default.Rockin_k(_module._default.Rockin'$G: Ty, g#0: Box) : Box;

function _module.__default.Rockin_k#canCall(_module._default.Rockin'$G: Ty, g#0: Box) : bool;

// consequence axiom for _module.__default.Rockin_k
axiom 32 <= $FunctionContextHeight
   ==> (forall _module._default.Rockin'$G: Ty, g#0: Box :: 
    { _module.__default.Rockin_k(_module._default.Rockin'$G, g#0) } 
    _module.__default.Rockin_k#canCall(_module._default.Rockin'$G, g#0)
         || (32 != $FunctionContextHeight && $IsBox(g#0, _module._default.Rockin'$G))
       ==> $IsBox(_module.__default.Rockin_k(_module._default.Rockin'$G, g#0), 
        _module._default.Rockin'$G));

function _module.__default.Rockin_k#requires(Ty, Box) : bool;

// #requires axiom for _module.__default.Rockin_k
axiom (forall _module._default.Rockin'$G: Ty, g#0: Box :: 
  { _module.__default.Rockin_k#requires(_module._default.Rockin'$G, g#0) } 
  $IsBox(g#0, _module._default.Rockin'$G)
     ==> _module.__default.Rockin_k#requires(_module._default.Rockin'$G, g#0) == true);

// definition axiom for _module.__default.Rockin_k (revealed)
axiom 32 <= $FunctionContextHeight
   ==> (forall _module._default.Rockin'$G: Ty, g#0: Box :: 
    { _module.__default.Rockin_k(_module._default.Rockin'$G, g#0) } 
    _module.__default.Rockin_k#canCall(_module._default.Rockin'$G, g#0)
         || (32 != $FunctionContextHeight && $IsBox(g#0, _module._default.Rockin'$G))
       ==> _module.__default.Rockin_k(_module._default.Rockin'$G, g#0)
         == (var h#0 := g#0; h#0));

// definition axiom for _module.__default.Rockin_k for all literals (revealed)
axiom 32 <= $FunctionContextHeight
   ==> (forall _module._default.Rockin'$G: Ty, g#0: Box :: 
    {:weight 3} { _module.__default.Rockin_k(_module._default.Rockin'$G, Lit(g#0)) } 
    _module.__default.Rockin_k#canCall(_module._default.Rockin'$G, Lit(g#0))
         || (32 != $FunctionContextHeight && $IsBox(g#0, _module._default.Rockin'$G))
       ==> _module.__default.Rockin_k(_module._default.Rockin'$G, Lit(g#0))
         == (var h#1 := Lit(g#0); h#1));

procedure CheckWellformed$$_module.__default.Rockin_k(_module._default.Rockin'$G: Ty, 
    g#0: Box where $IsBox(g#0, _module._default.Rockin'$G));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.Groovy
function _module.__default.Groovy(_module._default.Groovy$G: Ty, g#0: Box, x#0: int) : Box;

function _module.__default.Groovy#canCall(_module._default.Groovy$G: Ty, g#0: Box, x#0: int) : bool;

// consequence axiom for _module.__default.Groovy
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.Groovy$G: Ty, g#0: Box, x#0: int :: 
    { _module.__default.Groovy(_module._default.Groovy$G, g#0, x#0) } 
    _module.__default.Groovy#canCall(_module._default.Groovy$G, g#0, x#0)
         || (30 != $FunctionContextHeight && $IsBox(g#0, _module._default.Groovy$G))
       ==> $IsBox(_module.__default.Groovy(_module._default.Groovy$G, g#0, x#0), 
        _module._default.Groovy$G));

function _module.__default.Groovy#requires(Ty, Box, int) : bool;

// #requires axiom for _module.__default.Groovy
axiom (forall _module._default.Groovy$G: Ty, g#0: Box, x#0: int :: 
  { _module.__default.Groovy#requires(_module._default.Groovy$G, g#0, x#0) } 
  $IsBox(g#0, _module._default.Groovy$G)
     ==> _module.__default.Groovy#requires(_module._default.Groovy$G, g#0, x#0) == true);

// definition axiom for _module.__default.Groovy (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.Groovy$G: Ty, g#0: Box, x#0: int :: 
    { _module.__default.Groovy(_module._default.Groovy$G, g#0, x#0) } 
    _module.__default.Groovy#canCall(_module._default.Groovy$G, g#0, x#0)
         || (30 != $FunctionContextHeight && $IsBox(g#0, _module._default.Groovy$G))
       ==> (var h#0 := g#0; 
          x#0 == LitInt(80)
             ==> _module.__default.RogerThat#canCall(_module._default.Groovy$G, h#0))
         && _module.__default.Groovy(_module._default.Groovy$G, g#0, x#0)
           == (var h#0 := g#0; 
            (if x#0 == LitInt(80)
               then _module.__default.RogerThat(_module._default.Groovy$G, h#0)
               else Seq#Index(Seq#Build(Seq#Empty(): Seq Box, h#0), LitInt(0)))));

// definition axiom for _module.__default.Groovy for decreasing-related literals (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.Groovy$G: Ty, g#0: Box, x#0: int :: 
    {:weight 3} { _module.__default.Groovy(_module._default.Groovy$G, g#0, LitInt(x#0)) } 
    _module.__default.Groovy#canCall(_module._default.Groovy$G, g#0, LitInt(x#0))
         || (30 != $FunctionContextHeight && $IsBox(g#0, _module._default.Groovy$G))
       ==> (var h#1 := g#0; 
          LitInt(x#0) == LitInt(80)
             ==> _module.__default.RogerThat#canCall(_module._default.Groovy$G, h#1))
         && _module.__default.Groovy(_module._default.Groovy$G, g#0, LitInt(x#0))
           == (var h#1 := g#0; 
            (if LitInt(x#0) == LitInt(80)
               then _module.__default.RogerThat(_module._default.Groovy$G, h#1)
               else Seq#Index(Seq#Build(Seq#Empty(): Seq Box, h#1), LitInt(0)))));

// definition axiom for _module.__default.Groovy for all literals (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall _module._default.Groovy$G: Ty, g#0: Box, x#0: int :: 
    {:weight 3} { _module.__default.Groovy(_module._default.Groovy$G, Lit(g#0), LitInt(x#0)) } 
    _module.__default.Groovy#canCall(_module._default.Groovy$G, Lit(g#0), LitInt(x#0))
         || (30 != $FunctionContextHeight && $IsBox(g#0, _module._default.Groovy$G))
       ==> (var h#2 := Lit(g#0); 
          LitInt(x#0) == LitInt(80)
             ==> _module.__default.RogerThat#canCall(_module._default.Groovy$G, h#2))
         && _module.__default.Groovy(_module._default.Groovy$G, Lit(g#0), LitInt(x#0))
           == (var h#2 := Lit(g#0); 
            (if LitInt(x#0) == LitInt(80)
               then _module.__default.RogerThat(_module._default.Groovy$G, h#2)
               else Seq#Index(Lit(Seq#Build(Seq#Empty(): Seq Box, h#2)), LitInt(0)))));

procedure CheckWellformed$$_module.__default.Groovy(_module._default.Groovy$G: Ty, 
    g#0: Box where $IsBox(g#0, _module._default.Groovy$G), 
    x#0: int);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Groovy(_module._default.Groovy$G: Ty, g#0: Box, x#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var h#Z#0: Box;
  var let#0#0#0: Box;
  var ##g#0: Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Groovy
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(140,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    if (*)
    {
        assume $IsBox(_module.__default.Groovy(_module._default.Groovy$G, g#0, x#0), 
          _module._default.Groovy$G);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        havoc h#Z#0;
        assume $IsBox(h#Z#0, _module._default.Groovy$G);
        assume let#0#0#0 == g#0;
        assume true;
        // CheckWellformedWithResult: any expression
        assume $IsBox(let#0#0#0, _module._default.Groovy$G);
        assume h#Z#0 == let#0#0#0;
        if (x#0 == LitInt(80))
        {
            ##g#0 := h#Z#0;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##g#0, _module._default.Groovy$G, $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.RogerThat#canCall(_module._default.Groovy$G, h#Z#0);
            assume _module.__default.Groovy(_module._default.Groovy$G, g#0, x#0)
               == _module.__default.RogerThat(_module._default.Groovy$G, h#Z#0);
            assume _module.__default.RogerThat#canCall(_module._default.Groovy$G, h#Z#0);
            // CheckWellformedWithResult: any expression
            assume $IsBox(_module.__default.Groovy(_module._default.Groovy$G, g#0, x#0), 
              _module._default.Groovy$G);
        }
        else
        {
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(Seq#Build(Seq#Empty(): Seq Box, h#Z#0));
            assume _module.__default.Groovy(_module._default.Groovy$G, g#0, x#0)
               == Seq#Index(Seq#Build(Seq#Empty(): Seq Box, h#Z#0), LitInt(0));
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(_module.__default.Groovy(_module._default.Groovy$G, g#0, x#0), 
              _module._default.Groovy$G);
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.IsRogerCool(n#0: int);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.IsRogerCool(n#0: int);
  // user-defined preconditions
  requires _module.__default.RogerThat#canCall(TBool, $Box(Lit(true)))
     ==> Lit($Unbox(_module.__default.RogerThat(TBool, $Box(Lit(true)))): bool)
       || Lit(true);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.IsRogerCool(n#0: int) returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.RogerThat#canCall(TBool, $Box(Lit(true)))
     && 
    Lit($Unbox(_module.__default.RogerThat(TBool, $Box(Lit(true)))): bool)
     && Lit(true);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.IsRogerCool(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b#0_0: bool;
  var ##g#1_0: bool;
  var ##g#2_0: bool;
  var ##g#3_0: bool;
  var ##x#3_0: int;
  var ##g#4_0: bool;
  var ##x#4_0: int;

    // AddMethodImpl: IsRogerCool, Impl$$_module.__default.IsRogerCool
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(151,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(152,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(153,5)
        if (Lit(2 < 3))
        {
        }

        if (2 < 3 && n#0 < n#0)
        {
        }

        ##b#0_0 := 2 < 3 && n#0 < n#0 && n#0 < n#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0_0, TBool, $Heap);
        assume _module.__default.Cool#canCall(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1);
        assume _module.__default.Cool#canCall(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1);
        assert {:subsumption 0} _module.__default.Cool#canCall(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1)
           ==> _module.__default.Cool(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1) || Lit(2 < 3);
        assert {:subsumption 0} _module.__default.Cool#canCall(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1)
           ==> _module.__default.Cool(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1) || n#0 < n#0;
        assert {:subsumption 0} _module.__default.Cool#canCall(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1)
           ==> _module.__default.Cool(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1) || n#0 < n#0 + 1;
        assume _module.__default.Cool(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1);
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(154,10)
        if (*)
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(155,5)
            if (Lit(2 < 3))
            {
            }

            if (2 < 3 && n#0 < n#0)
            {
            }

            ##g#1_0 := 2 < 3 && n#0 < n#0 && n#0 < n#0 + 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##g#1_0, TBool, $Heap);
            assume _module.__default.RogerThat#canCall(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1));
            assume _module.__default.RogerThat#canCall(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1));
            assert {:subsumption 0} _module.__default.RogerThat#canCall(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1))
               ==> $Unbox(_module.__default.RogerThat(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1))): bool
                 || Lit(2 < 3);
            assert {:subsumption 0} _module.__default.RogerThat#canCall(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1))
               ==> $Unbox(_module.__default.RogerThat(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1))): bool
                 || n#0 < n#0;
            assert {:subsumption 0} _module.__default.RogerThat#canCall(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1))
               ==> $Unbox(_module.__default.RogerThat(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1))): bool
                 || n#0 < n#0 + 1;
            assume $Unbox(_module.__default.RogerThat(TBool, $Box(2 < 3 && n#0 < n#0 && n#0 < n#0 + 1))): bool;
        }
        else
        {
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(156,10)
            if (*)
            {
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(157,5)
                ##g#2_0 := Lit(false);
                // assume allocatedness for argument to function
                assume $IsAlloc(##g#2_0, TBool, $Heap);
                assume _module.__default.Rockin_k#canCall(TBool, $Box(Lit(false)));
                assume _module.__default.Rockin_k#canCall(TBool, $Box(Lit(false)));
                assert {:subsumption 0} _module.__default.Rockin_k#canCall(TBool, $Box(Lit(false)))
                   ==> Lit($Unbox(_module.__default.Rockin_k(TBool, $Box(Lit(false)))): bool)
                     || (var h#2_0 := Lit(false); h#2_0);
                assume $Unbox(_module.__default.Rockin_k(TBool, $Box(Lit(false)))): bool;
            }
            else
            {
                // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(158,10)
                if (*)
                {
                    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(159,5)
                    ##g#3_0 := n#0 < n#0;
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##g#3_0, TBool, $Heap);
                    ##x#3_0 := LitInt(80);
                    // assume allocatedness for argument to function
                    assume $IsAlloc(##x#3_0, TInt, $Heap);
                    assume _module.__default.Groovy#canCall(TBool, $Box(n#0 < n#0), LitInt(80));
                    assume _module.__default.Groovy#canCall(TBool, $Box(n#0 < n#0), LitInt(80));
                    assert {:subsumption 0} _module.__default.Groovy#canCall(TBool, $Box(n#0 < n#0), LitInt(80))
                       ==> $Unbox(_module.__default.Groovy(TBool, $Box(n#0 < n#0), LitInt(80))): bool
                         || (var h#3_0 := n#0 < n#0; 
                          LitInt(80) == LitInt(80)
                             ==> 
                            _module.__default.RogerThat#canCall(TBool, $Box(h#3_0))
                             ==> $Unbox(_module.__default.RogerThat(TBool, $Box(h#3_0))): bool || h#3_0);
                    assert {:subsumption 0} _module.__default.Groovy#canCall(TBool, $Box(n#0 < n#0), LitInt(80))
                       ==> $Unbox(_module.__default.Groovy(TBool, $Box(n#0 < n#0), LitInt(80))): bool
                         || (var h#3_0 := n#0 < n#0; 
                          LitInt(80) != LitInt(80)
                             ==> $Unbox(Seq#Index(Seq#Build(Seq#Empty(): Seq Box, $Box(h#3_0)), LitInt(0))): bool);
                    assume $Unbox(_module.__default.Groovy(TBool, $Box(n#0 < n#0), LitInt(80))): bool;
                }
                else
                {
                    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(160,10)
                    if (*)
                    {
                        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(161,5)
                        ##g#4_0 := n#0 + 1 <= n#0;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##g#4_0, TBool, $Heap);
                        ##x#4_0 := LitInt(81);
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##x#4_0, TInt, $Heap);
                        assume _module.__default.Groovy#canCall(TBool, $Box(n#0 + 1 <= n#0), LitInt(81));
                        assume _module.__default.Groovy#canCall(TBool, $Box(n#0 + 1 <= n#0), LitInt(81));
                        assert {:subsumption 0} _module.__default.Groovy#canCall(TBool, $Box(n#0 + 1 <= n#0), LitInt(81))
                           ==> $Unbox(_module.__default.Groovy(TBool, $Box(n#0 + 1 <= n#0), LitInt(81))): bool
                             || (var h#4_0 := n#0 + 1 <= n#0; 
                              LitInt(81) == LitInt(80)
                                 ==> 
                                _module.__default.RogerThat#canCall(TBool, $Box(h#4_0))
                                 ==> $Unbox(_module.__default.RogerThat(TBool, $Box(h#4_0))): bool || h#4_0);
                        assert {:subsumption 0} _module.__default.Groovy#canCall(TBool, $Box(n#0 + 1 <= n#0), LitInt(81))
                           ==> $Unbox(_module.__default.Groovy(TBool, $Box(n#0 + 1 <= n#0), LitInt(81))): bool
                             || (var h#4_0 := n#0 + 1 <= n#0; 
                              LitInt(81) != LitInt(80)
                                 ==> $Unbox(Seq#Index(Seq#Build(Seq#Empty(): Seq Box, $Box(h#4_0)), LitInt(0))): bool);
                        assume $Unbox(_module.__default.Groovy(TBool, $Box(n#0 + 1 <= n#0), LitInt(81))): bool;
                    }
                    else
                    {
                    }
                }
            }
        }
    }
}



procedure CheckWellformed$$_module.__default.LoopyRoger(n#0: int);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.LoopyRoger(n#0: int);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.LoopyRoger(n#0: int) returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.LoopyRoger(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var ##g#0: bool;
  var $decr$loop#00: int;
  var $PreLoopHeap$loop#1: Heap;
  var $decr_init$loop#10: int;
  var $w$loop#1: bool;
  var ##g#1: bool;
  var $decr$loop#10: int;

    // AddMethodImpl: LoopyRoger, Impl$$_module.__default.LoopyRoger
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(166,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(167,9)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(167,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(168,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := n#0 - i#0;
    havoc $w$loop#0;
    while (true)
      free invariant $w$loop#0
         ==> _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0));
      invariant $w$loop#0
         ==> 
        _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))
         ==> $Unbox(_module.__default.RogerThat(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))): bool
           || (LitInt(0) <= n#0 ==> i#0 <= n#0);
      free invariant $w$loop#0
         ==> _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))
           && 
          $Unbox(_module.__default.RogerThat(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))): bool
           && (LitInt(0) <= n#0 ==> i#0 <= n#0);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#0[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#0, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#0, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
      free invariant n#0 - i#0 <= $decr_init$loop#00 && (n#0 - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(168,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            if (LitInt(0) <= n#0)
            {
            }

            ##g#0 := LitInt(0) <= n#0 ==> i#0 <= n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##g#0, TBool, $Heap);
            assume _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0));
            assume _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0));
            assume $Unbox(_module.__default.RogerThat(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))): bool;
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#0)
        {
            break;
        }

        $decr$loop#00 := n#0 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(171,7)
        assume true;
        assume true;
        i#0 := i#0 + 1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(171,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(168,3)
        assert 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert n#0 - i#0 < $decr$loop#00;
        assume _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0));
    }

    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(173,5)
    assume true;
    assume true;
    i#0 := LitInt(0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(173,8)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(174,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#1 := $Heap;
    $decr_init$loop#10 := n#0 - i#0;
    havoc $w$loop#1;
    while (true)
      free invariant $w$loop#1
         ==> _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0));
      invariant $w$loop#1
         ==> 
        _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))
         ==> $Unbox(_module.__default.RogerThat(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))): bool
           || (LitInt(0) <= n#0 ==> i#0 <= n#0);
      free invariant $w$loop#1
         ==> _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))
           && 
          $Unbox(_module.__default.RogerThat(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))): bool
           && (LitInt(0) <= n#0 ==> i#0 <= n#0);
      free invariant (forall $o: ref :: 
        { $Heap[$o] } 
        $o != null && read(old($Heap), $o, alloc)
           ==> $Heap[$o] == $PreLoopHeap$loop#1[$o]);
      free invariant $HeapSucc($PreLoopHeap$loop#1, $Heap);
      free invariant (forall<alpha> $o: ref, $f: Field alpha :: 
        { read($Heap, $o, $f) } 
        $o != null && read($PreLoopHeap$loop#1, $o, alloc)
           ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#1, $o, $f) || $_Frame[$o, $f]);
      free invariant n#0 - i#0 <= $decr_init$loop#10 && (n#0 - i#0 == $decr_init$loop#10 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(174,2): after some loop iterations"} true;
        if (!$w$loop#1)
        {
            if (LitInt(0) <= n#0)
            {
            }

            ##g#1 := LitInt(0) <= n#0 ==> i#0 <= n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##g#1, TBool, $Heap);
            assume _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0));
            assume _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0));
            assume $Unbox(_module.__default.RogerThat(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0))): bool;
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#0)
        {
            break;
        }

        $decr$loop#10 := n#0 - i#0;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(177,7)
        assume true;
        assume true;
        i#0 := i#0 + 2;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(177,14)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(174,3)
        assert 0 <= $decr$loop#10 || n#0 - i#0 == $decr$loop#10;
        assert n#0 - i#0 < $decr$loop#10;
        assume _module.__default.RogerThat#canCall(TBool, $Box(LitInt(0) <= n#0 ==> i#0 <= n#0));
    }
}



procedure CheckWellformed$$_module.__default.TyKn__Main(k0#0: ref
       where $Is(k0#0, Tclass._module.TyKn__K?())
         && $IsAlloc(k0#0, Tclass._module.TyKn__K?(), $Heap));
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.TyKn__Main(k0#0: ref
       where $Is(k0#0, Tclass._module.TyKn__K?())
         && $IsAlloc(k0#0, Tclass._module.TyKn__K?(), $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.TyKn__Main(k0#0: ref
       where $Is(k0#0, Tclass._module.TyKn__K?())
         && $IsAlloc(k0#0, Tclass._module.TyKn__K?(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.TyKn__Main(k0#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var c#0: ref
     where $Is(c#0, Tclass._module.TyKn__C(Tclass._module.TyKn__K?()))
       && $IsAlloc(c#0, Tclass._module.TyKn__C(Tclass._module.TyKn__K?()), $Heap);
  var $nw: ref;
  var k1#0: ref
     where $Is(k1#0, Tclass._module.TyKn__K?())
       && $IsAlloc(k1#0, Tclass._module.TyKn__K?(), $Heap);
  var k2#0: ref
     where $Is(k2#0, Tclass._module.TyKn__K?())
       && $IsAlloc(k2#0, Tclass._module.TyKn__K?(), $Heap);
  var $rhs##0: ref
     where $Is($rhs##0, Tclass._module.TyKn__K?())
       && $IsAlloc($rhs##0, Tclass._module.TyKn__K?(), $Heap);
  var $tmp##0: Box;

    // AddMethodImpl: TyKn_Main, Impl$$_module.__default.TyKn__Main
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(200,30): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(201,9)
    assume true;
    havoc $nw;
    assume $nw != null && dtype($nw) == Tclass._module.TyKn__C?(Tclass._module.TyKn__K?());
    assume !read($Heap, $nw, alloc);
    $Heap := update($Heap, $nw, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    c#0 := $nw;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(201,30)"} true;
    havoc k1#0 /* where $Is(k1#0, Tclass._module.TyKn__K?())
       && $IsAlloc(k1#0, Tclass._module.TyKn__K?(), $Heap) */;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(204,3)
    if (k0#0 != null)
    {
        assert {:subsumption 0} k0#0 != null;
        assume _module.TyKn__K.F#canCall(k0#0);
    }

    assume k0#0 != null ==> _module.TyKn__K.F#canCall(k0#0);
    assert {:subsumption 0} k0#0 != null ==> LitInt(_module.TyKn__K.F(k0#0)) == LitInt(176);
    assume k0#0 != null ==> LitInt(_module.TyKn__K.F(k0#0)) == LitInt(176);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(205,3)
    if (k1#0 != null)
    {
        assert {:subsumption 0} k1#0 != null;
        assume _module.TyKn__K.F#canCall(k1#0);
    }

    assume k1#0 != null ==> _module.TyKn__K.F#canCall(k1#0);
    assert {:subsumption 0} k1#0 != null ==> LitInt(_module.TyKn__K.F(k1#0)) == LitInt(176);
    assume k1#0 != null ==> LitInt(_module.TyKn__K.F(k1#0)) == LitInt(176);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(207,3)
    assert {:subsumption 0} c#0 != null;
    if ($Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref != null)
    {
        assert {:subsumption 0} c#0 != null;
        assert {:subsumption 0} $Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref != null;
        assume _module.TyKn__K.F#canCall($Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref);
    }

    assume $Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref != null
       ==> _module.TyKn__K.F#canCall($Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref);
    assert {:subsumption 0} $Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref != null
       ==> LitInt(_module.TyKn__K.F($Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref))
         == LitInt(176);
    assume $Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref != null
       ==> LitInt(_module.TyKn__K.F($Unbox(read($Heap, c#0, _module.TyKn__C.x)): ref))
         == LitInt(176);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(208,3)
    assert {:subsumption 0} c#0 != null;
    assume _module.TyKn__C.G#canCall(Tclass._module.TyKn__K?(), $Heap, c#0);
    if ($Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref != null)
    {
        assert {:subsumption 0} c#0 != null;
        assume _module.TyKn__C.G#canCall(Tclass._module.TyKn__K?(), $Heap, c#0);
        assert {:subsumption 0} $Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref != null;
        assume _module.TyKn__K.F#canCall($Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref);
    }

    assume _module.TyKn__C.G#canCall(Tclass._module.TyKn__K?(), $Heap, c#0)
       && ($Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref != null
         ==> _module.TyKn__C.G#canCall(Tclass._module.TyKn__K?(), $Heap, c#0)
           && _module.TyKn__K.F#canCall($Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref));
    assert {:subsumption 0} $Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref != null
       ==> LitInt(_module.TyKn__K.F($Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref))
         == LitInt(176);
    assume $Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref != null
       ==> LitInt(_module.TyKn__K.F($Unbox(_module.TyKn__C.G(Tclass._module.TyKn__K?(), $Heap, c#0)): ref))
         == LitInt(176);
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(209,16)
    assume true;
    // TrCallStmt: Adding lhs with type TyKn_K?
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    assert c#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $tmp##0 := Call$$_module.TyKn__C.M(Tclass._module.TyKn__K?(), c#0);
    havoc $rhs##0;
    assume $rhs##0 == $Unbox($tmp##0): ref;
    // TrCallStmt: After ProcessCallStmt
    k2#0 := $rhs##0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(209,17)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(210,3)
    if (k2#0 != null)
    {
        assert {:subsumption 0} k2#0 != null;
        assume _module.TyKn__K.F#canCall(k2#0);
    }

    assume k2#0 != null ==> _module.TyKn__K.F#canCall(k2#0);
    assert {:subsumption 0} k2#0 != null ==> LitInt(_module.TyKn__K.F(k2#0)) == LitInt(176);
    assume k2#0 != null ==> LitInt(_module.TyKn__K.F(k2#0)) == LitInt(176);
}



// function declaration for _module._default.InList
function _module.__default.InList(_module._default.InList$T: Ty, x#0: Box, xs#0: DatatypeType) : bool;

function _module.__default.InList#canCall(_module._default.InList$T: Ty, x#0: Box, xs#0: DatatypeType) : bool;

// consequence axiom for _module.__default.InList
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.InList$T: Ty, x#0: Box, xs#0: DatatypeType :: 
    { _module.__default.InList(_module._default.InList$T, x#0, xs#0) } 
    _module.__default.InList#canCall(_module._default.InList$T, x#0, xs#0)
         || (3 != $FunctionContextHeight
           && 
          $IsBox(x#0, _module._default.InList$T)
           && $Is(xs#0, Tclass._module.List(_module._default.InList$T)))
       ==> true);

function _module.__default.InList#requires(Ty, Box, DatatypeType) : bool;

// #requires axiom for _module.__default.InList
axiom (forall _module._default.InList$T: Ty, x#0: Box, xs#0: DatatypeType :: 
  { _module.__default.InList#requires(_module._default.InList$T, x#0, xs#0) } 
  $IsBox(x#0, _module._default.InList$T)
       && $Is(xs#0, Tclass._module.List(_module._default.InList$T))
     ==> _module.__default.InList#requires(_module._default.InList$T, x#0, xs#0) == true);

procedure CheckWellformed$$_module.__default.InList(_module._default.InList$T: Ty, 
    x#0: Box where $IsBox(x#0, _module._default.InList$T), 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.InList$T)));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.Subset
function _module.__default.Subset(_module._default.Subset$T: Ty, xs#0: DatatypeType, ys#0: DatatypeType) : bool;

function _module.__default.Subset#canCall(_module._default.Subset$T: Ty, xs#0: DatatypeType, ys#0: DatatypeType) : bool;

// consequence axiom for _module.__default.Subset
axiom 4 <= $FunctionContextHeight
   ==> (forall _module._default.Subset$T: Ty, xs#0: DatatypeType, ys#0: DatatypeType :: 
    { _module.__default.Subset(_module._default.Subset$T, xs#0, ys#0) } 
    _module.__default.Subset#canCall(_module._default.Subset$T, xs#0, ys#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(xs#0, Tclass._module.List(_module._default.Subset$T))
           && $Is(ys#0, Tclass._module.List(_module._default.Subset$T)))
       ==> true);

function _module.__default.Subset#requires(Ty, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Subset
axiom (forall _module._default.Subset$T: Ty, xs#0: DatatypeType, ys#0: DatatypeType :: 
  { _module.__default.Subset#requires(_module._default.Subset$T, xs#0, ys#0) } 
  $Is(xs#0, Tclass._module.List(_module._default.Subset$T))
       && $Is(ys#0, Tclass._module.List(_module._default.Subset$T))
     ==> _module.__default.Subset#requires(_module._default.Subset$T, xs#0, ys#0) == true);

// definition axiom for _module.__default.Subset (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall _module._default.Subset$T: Ty, xs#0: DatatypeType, ys#0: DatatypeType :: 
    { _module.__default.Subset(_module._default.Subset$T, xs#0, ys#0) } 
    _module.__default.Subset#canCall(_module._default.Subset$T, xs#0, ys#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(xs#0, Tclass._module.List(_module._default.Subset$T))
           && $Is(ys#0, Tclass._module.List(_module._default.Subset$T)))
       ==> (forall x#0: Box :: 
          { _module.__default.InList(_module._default.Subset$T, x#0, ys#0) } 
            { _module.__default.InList(_module._default.Subset$T, x#0, xs#0) } 
          $IsBox(x#0, _module._default.Subset$T)
             ==> _module.__default.InList#canCall(_module._default.Subset$T, x#0, xs#0)
               && (_module.__default.InList(_module._default.Subset$T, x#0, xs#0)
                 ==> _module.__default.InList#canCall(_module._default.Subset$T, x#0, ys#0)))
         && _module.__default.Subset(_module._default.Subset$T, xs#0, ys#0)
           == (forall x#0: Box :: 
            { _module.__default.InList(_module._default.Subset$T, x#0, ys#0) } 
              { _module.__default.InList(_module._default.Subset$T, x#0, xs#0) } 
            $IsBox(x#0, _module._default.Subset$T)
               ==> 
              _module.__default.InList(_module._default.Subset$T, x#0, xs#0)
               ==> _module.__default.InList(_module._default.Subset$T, x#0, ys#0)));

// definition axiom for _module.__default.Subset for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall _module._default.Subset$T: Ty, xs#0: DatatypeType, ys#0: DatatypeType :: 
    {:weight 3} { _module.__default.Subset(_module._default.Subset$T, Lit(xs#0), Lit(ys#0)) } 
    _module.__default.Subset#canCall(_module._default.Subset$T, Lit(xs#0), Lit(ys#0))
         || (4 != $FunctionContextHeight
           && 
          $Is(xs#0, Tclass._module.List(_module._default.Subset$T))
           && $Is(ys#0, Tclass._module.List(_module._default.Subset$T)))
       ==> (forall x#1: Box :: 
          { _module.__default.InList(_module._default.Subset$T, x#1, ys#0) } 
            { _module.__default.InList(_module._default.Subset$T, x#1, xs#0) } 
          $IsBox(x#1, _module._default.Subset$T)
             ==> _module.__default.InList#canCall(_module._default.Subset$T, x#1, Lit(xs#0))
               && (_module.__default.InList(_module._default.Subset$T, x#1, Lit(xs#0))
                 ==> _module.__default.InList#canCall(_module._default.Subset$T, x#1, Lit(ys#0))))
         && _module.__default.Subset(_module._default.Subset$T, Lit(xs#0), Lit(ys#0))
           == (forall x#1: Box :: 
            { _module.__default.InList(_module._default.Subset$T, x#1, ys#0) } 
              { _module.__default.InList(_module._default.Subset$T, x#1, xs#0) } 
            $IsBox(x#1, _module._default.Subset$T)
               ==> 
              _module.__default.InList(_module._default.Subset$T, x#1, Lit(xs#0))
               ==> _module.__default.InList(_module._default.Subset$T, x#1, Lit(ys#0))));

procedure CheckWellformed$$_module.__default.Subset(_module._default.Subset$T: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.Subset$T)), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(_module._default.Subset$T)));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Subset(_module._default.Subset$T: Ty, xs#0: DatatypeType, ys#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#2: Box;
  var ##x#0: Box;
  var ##xs#0: DatatypeType;
  var ##x#1: Box;
  var ##xs#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function Subset
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(246,10): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        // Begin Comprehension WF check
        havoc x#2;
        if ($IsBox(x#2, _module._default.Subset$T))
        {
            ##x#0 := x#2;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#0, _module._default.Subset$T, $Heap);
            ##xs#0 := xs#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(_module._default.Subset$T), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume _module.__default.InList#canCall(_module._default.Subset$T, x#2, xs#0);
            if (_module.__default.InList(_module._default.Subset$T, x#2, xs#0))
            {
                ##x#1 := x#2;
                // assume allocatedness for argument to function
                assume $IsAllocBox(##x#1, _module._default.Subset$T, $Heap);
                ##xs#1 := ys#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##xs#1, Tclass._module.List(_module._default.Subset$T), $Heap);
                b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assume _module.__default.InList#canCall(_module._default.Subset$T, x#2, ys#0);
            }
        }

        // End Comprehension WF check
        assume _module.__default.Subset(_module._default.Subset$T, xs#0, ys#0)
           == (forall x#3: Box :: 
            { _module.__default.InList(_module._default.Subset$T, x#3, ys#0) } 
              { _module.__default.InList(_module._default.Subset$T, x#3, xs#0) } 
            $IsBox(x#3, _module._default.Subset$T)
               ==> 
              _module.__default.InList(_module._default.Subset$T, x#3, xs#0)
               ==> _module.__default.InList(_module._default.Subset$T, x#3, ys#0));
        assume (forall x#3: Box :: 
          { _module.__default.InList(_module._default.Subset$T, x#3, ys#0) } 
            { _module.__default.InList(_module._default.Subset$T, x#3, xs#0) } 
          $IsBox(x#3, _module._default.Subset$T)
             ==> _module.__default.InList#canCall(_module._default.Subset$T, x#3, xs#0)
               && (_module.__default.InList(_module._default.Subset$T, x#3, xs#0)
                 ==> _module.__default.InList#canCall(_module._default.Subset$T, x#3, ys#0)));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Subset(_module._default.Subset$T, xs#0, ys#0), TBool);
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.ListLemma__T(_module._default.ListLemma_T$T: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.ListLemma_T$T))
         && $IsAlloc(xs#0, Tclass._module.List(_module._default.ListLemma_T$T), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(_module._default.ListLemma_T$T))
         && $IsAlloc(ys#0, Tclass._module.List(_module._default.ListLemma_T$T), $Heap)
         && $IsA#_module.List(ys#0));
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ListLemma__T(_module._default.ListLemma_T$T: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.ListLemma_T$T))
         && $IsAlloc(xs#0, Tclass._module.List(_module._default.ListLemma_T$T), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(_module._default.ListLemma_T$T))
         && $IsAlloc(ys#0, Tclass._module.List(_module._default.ListLemma_T$T), $Heap)
         && $IsA#_module.List(ys#0));
  // user-defined preconditions
  requires (forall x#1: Box :: 
    { _module.__default.InList(_module._default.ListLemma_T$T, x#1, ys#0) } 
      { _module.__default.InList(_module._default.ListLemma_T$T, x#1, xs#0) } 
    $IsBox(x#1, _module._default.ListLemma_T$T)
       ==> 
      _module.__default.InList(_module._default.ListLemma_T$T, x#1, xs#0)
       ==> _module.__default.InList(_module._default.ListLemma_T$T, x#1, ys#0));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.ListLemma__T(_module._default.ListLemma_T$T: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.ListLemma_T$T))
         && $IsAlloc(xs#0, Tclass._module.List(_module._default.ListLemma_T$T), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(_module._default.ListLemma_T$T))
         && $IsAlloc(ys#0, Tclass._module.List(_module._default.ListLemma_T$T), $Heap)
         && $IsA#_module.List(ys#0))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall x#1: Box :: 
    { _module.__default.InList(_module._default.ListLemma_T$T, x#1, ys#0) } 
      { _module.__default.InList(_module._default.ListLemma_T$T, x#1, xs#0) } 
    $IsBox(x#1, _module._default.ListLemma_T$T)
       ==> 
      _module.__default.InList(_module._default.ListLemma_T$T, x#1, xs#0)
       ==> _module.__default.InList(_module._default.ListLemma_T$T, x#1, ys#0));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.ListLemma__T(_module._default.ListLemma_T$T: Ty, xs#0: DatatypeType, ys#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##xs#2: DatatypeType;
  var ##ys#0: DatatypeType;

    // AddMethodImpl: ListLemma_T, Impl$$_module.__default.ListLemma__T
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(252,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(253,3)
    ##xs#2 := xs#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##xs#2, Tclass._module.List(_module._default.ListLemma_T$T), $Heap);
    ##ys#0 := ys#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##ys#0, Tclass._module.List(_module._default.ListLemma_T$T), $Heap);
    assume _module.__default.Subset#canCall(_module._default.ListLemma_T$T, xs#0, ys#0);
    assume _module.__default.Subset#canCall(_module._default.ListLemma_T$T, xs#0, ys#0);
    assert {:subsumption 0} _module.__default.Subset#canCall(_module._default.ListLemma_T$T, xs#0, ys#0)
       ==> _module.__default.Subset(_module._default.ListLemma_T$T, xs#0, ys#0)
         || (forall x#2: Box :: 
          { _module.__default.InList(_module._default.ListLemma_T$T, x#2, ys#0) } 
            { _module.__default.InList(_module._default.ListLemma_T$T, x#2, xs#0) } 
          $IsBox(x#2, _module._default.ListLemma_T$T)
             ==> 
            _module.__default.InList(_module._default.ListLemma_T$T, x#2, xs#0)
             ==> _module.__default.InList(_module._default.ListLemma_T$T, x#2, ys#0));
    assume _module.__default.Subset(_module._default.ListLemma_T$T, xs#0, ys#0);
}



procedure CheckWellformed$$_module.__default.ammeLtsiL__T(_module._default.ammeLtsiL_T$_T0: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0))
         && $IsAlloc(xs#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0))
         && $IsAlloc(ys#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0), $Heap)
         && $IsA#_module.List(ys#0));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ammeLtsiL__T(_module._default.ammeLtsiL_T$_T0: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0))
         && $IsAlloc(xs#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0))
         && $IsAlloc(ys#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0), $Heap)
         && $IsA#_module.List(ys#0));
  // user-defined preconditions
  requires _module.__default.Subset#canCall(_module._default.ammeLtsiL_T$_T0, xs#0, ys#0)
     ==> _module.__default.Subset(_module._default.ammeLtsiL_T$_T0, xs#0, ys#0)
       || (forall x#0: Box :: 
        { _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#0, ys#0) } 
          { _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#0, xs#0) } 
        $IsBox(x#0, _module._default.ammeLtsiL_T$_T0)
           ==> 
          _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#0, xs#0)
           ==> _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#0, ys#0));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.ammeLtsiL__T(_module._default.ammeLtsiL_T$_T0: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0))
         && $IsAlloc(xs#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0))
         && $IsAlloc(ys#0, Tclass._module.List(_module._default.ammeLtsiL_T$_T0), $Heap)
         && $IsA#_module.List(ys#0))
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Subset#canCall(_module._default.ammeLtsiL_T$_T0, xs#0, ys#0)
     && 
    _module.__default.Subset(_module._default.ammeLtsiL_T$_T0, xs#0, ys#0)
     && (forall x#1: Box :: 
      { _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#1, ys#0) } 
        { _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#1, xs#0) } 
      $IsBox(x#1, _module._default.ammeLtsiL_T$_T0)
         ==> 
        _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#1, xs#0)
         ==> _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#1, ys#0));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.ammeLtsiL__T(_module._default.ammeLtsiL_T$_T0: Ty, xs#0: DatatypeType, ys#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#2: Box;
  var ##x#0: Box;
  var ##xs#1: DatatypeType;
  var ##x#1: Box;
  var ##xs#2: DatatypeType;

    // AddMethodImpl: ammeLtsiL_T, Impl$$_module.__default.ammeLtsiL__T
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(257,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(258,3)
    // Begin Comprehension WF check
    havoc x#2;
    if ($IsBox(x#2, _module._default.ammeLtsiL_T$_T0))
    {
        ##x#0 := x#2;
        // assume allocatedness for argument to function
        assume $IsAllocBox(##x#0, _module._default.ammeLtsiL_T$_T0, $Heap);
        ##xs#1 := xs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#1, Tclass._module.List(_module._default.ammeLtsiL_T$_T0), $Heap);
        assume _module.__default.InList#canCall(_module._default.ammeLtsiL_T$_T0, x#2, xs#0);
        if (_module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#2, xs#0))
        {
            ##x#1 := x#2;
            // assume allocatedness for argument to function
            assume $IsAllocBox(##x#1, _module._default.ammeLtsiL_T$_T0, $Heap);
            ##xs#2 := ys#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#2, Tclass._module.List(_module._default.ammeLtsiL_T$_T0), $Heap);
            assume _module.__default.InList#canCall(_module._default.ammeLtsiL_T$_T0, x#2, ys#0);
        }
    }

    // End Comprehension WF check
    assume (forall x#3: Box :: 
      { _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#3, ys#0) } 
        { _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#3, xs#0) } 
      $IsBox(x#3, _module._default.ammeLtsiL_T$_T0)
         ==> _module.__default.InList#canCall(_module._default.ammeLtsiL_T$_T0, x#3, xs#0)
           && (_module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#3, xs#0)
             ==> _module.__default.InList#canCall(_module._default.ammeLtsiL_T$_T0, x#3, ys#0)));
    assert (forall x#3: Box :: 
      { _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#3, ys#0) } 
        { _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#3, xs#0) } 
      $IsBox(x#3, _module._default.ammeLtsiL_T$_T0)
         ==> 
        _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#3, xs#0)
         ==> _module.__default.InList(_module._default.ammeLtsiL_T$_T0, x#3, ys#0));
}



procedure CheckWellformed$$_module.__default.ListLemma__int(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(TInt))
         && $IsAlloc(xs#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(TInt))
         && $IsAlloc(ys#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(ys#0));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ListLemma__int(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(TInt))
         && $IsAlloc(xs#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(TInt))
         && $IsAlloc(ys#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(ys#0));
  // user-defined preconditions
  requires (forall x#1: int :: 
    { _module.__default.InList(TInt, $Box(x#1), ys#0) } 
      { _module.__default.InList(TInt, $Box(x#1), xs#0) } 
    true
       ==> 
      _module.__default.InList(TInt, $Box(x#1), xs#0)
       ==> _module.__default.InList(TInt, $Box(x#1), ys#0));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.ListLemma__int(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(TInt))
         && $IsAlloc(xs#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(TInt))
         && $IsAlloc(ys#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(ys#0))
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  // user-defined preconditions
  requires (forall x#1: int :: 
    { _module.__default.InList(TInt, $Box(x#1), ys#0) } 
      { _module.__default.InList(TInt, $Box(x#1), xs#0) } 
    true
       ==> 
      _module.__default.InList(TInt, $Box(x#1), xs#0)
       ==> _module.__default.InList(TInt, $Box(x#1), ys#0));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.ListLemma__int(xs#0: DatatypeType, ys#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##xs#2: DatatypeType;
  var ##ys#0: DatatypeType;

    // AddMethodImpl: ListLemma_int, Impl$$_module.__default.ListLemma__int
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(262,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(263,3)
    ##xs#2 := xs#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##xs#2, Tclass._module.List(TInt), $Heap);
    ##ys#0 := ys#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##ys#0, Tclass._module.List(TInt), $Heap);
    assume _module.__default.Subset#canCall(TInt, xs#0, ys#0);
    assume _module.__default.Subset#canCall(TInt, xs#0, ys#0);
    assert {:subsumption 0} _module.__default.Subset#canCall(TInt, xs#0, ys#0)
       ==> _module.__default.Subset(TInt, xs#0, ys#0)
         || (forall x#2: int :: 
          { _module.__default.InList(TInt, $Box(x#2), ys#0) } 
            { _module.__default.InList(TInt, $Box(x#2), xs#0) } 
          true
             ==> 
            _module.__default.InList(TInt, $Box(x#2), xs#0)
             ==> _module.__default.InList(TInt, $Box(x#2), ys#0));
    assume _module.__default.Subset(TInt, xs#0, ys#0);
}



procedure CheckWellformed$$_module.__default.ammeLtsiL__int(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(TInt))
         && $IsAlloc(xs#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(TInt))
         && $IsAlloc(ys#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(ys#0));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.ammeLtsiL__int(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(TInt))
         && $IsAlloc(xs#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(TInt))
         && $IsAlloc(ys#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(ys#0));
  // user-defined preconditions
  requires _module.__default.Subset#canCall(TInt, xs#0, ys#0)
     ==> _module.__default.Subset(TInt, xs#0, ys#0)
       || (forall x#0: int :: 
        { _module.__default.InList(TInt, $Box(x#0), ys#0) } 
          { _module.__default.InList(TInt, $Box(x#0), xs#0) } 
        true
           ==> 
          _module.__default.InList(TInt, $Box(x#0), xs#0)
           ==> _module.__default.InList(TInt, $Box(x#0), ys#0));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.ammeLtsiL__int(xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(TInt))
         && $IsAlloc(xs#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(xs#0), 
    ys#0: DatatypeType
       where $Is(ys#0, Tclass._module.List(TInt))
         && $IsAlloc(ys#0, Tclass._module.List(TInt), $Heap)
         && $IsA#_module.List(ys#0))
   returns ($_reverifyPost: bool);
  free requires 8 == $FunctionContextHeight;
  // user-defined preconditions
  free requires _module.__default.Subset#canCall(TInt, xs#0, ys#0)
     && 
    _module.__default.Subset(TInt, xs#0, ys#0)
     && (forall x#1: int :: 
      { _module.__default.InList(TInt, $Box(x#1), ys#0) } 
        { _module.__default.InList(TInt, $Box(x#1), xs#0) } 
      true
         ==> 
        _module.__default.InList(TInt, $Box(x#1), xs#0)
         ==> _module.__default.InList(TInt, $Box(x#1), ys#0));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.ammeLtsiL__int(xs#0: DatatypeType, ys#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#2: int;
  var ##x#0: int;
  var ##xs#1: DatatypeType;
  var ##x#1: int;
  var ##xs#2: DatatypeType;

    // AddMethodImpl: ammeLtsiL_int, Impl$$_module.__default.ammeLtsiL__int
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(267,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(268,3)
    // Begin Comprehension WF check
    havoc x#2;
    if (true)
    {
        ##x#0 := x#2;
        // assume allocatedness for argument to function
        assume $IsAlloc(##x#0, TInt, $Heap);
        ##xs#1 := xs#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##xs#1, Tclass._module.List(TInt), $Heap);
        assume _module.__default.InList#canCall(TInt, $Box(x#2), xs#0);
        if (_module.__default.InList(TInt, $Box(x#2), xs#0))
        {
            ##x#1 := x#2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##x#1, TInt, $Heap);
            ##xs#2 := ys#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#2, Tclass._module.List(TInt), $Heap);
            assume _module.__default.InList#canCall(TInt, $Box(x#2), ys#0);
        }
    }

    // End Comprehension WF check
    assume (forall x#3: int :: 
      { _module.__default.InList(TInt, $Box(x#3), ys#0) } 
        { _module.__default.InList(TInt, $Box(x#3), xs#0) } 
      _module.__default.InList#canCall(TInt, $Box(x#3), xs#0)
         && (_module.__default.InList(TInt, $Box(x#3), xs#0)
           ==> _module.__default.InList#canCall(TInt, $Box(x#3), ys#0)));
    assert (forall x#3: int :: 
      { _module.__default.InList(TInt, $Box(x#3), ys#0) } 
        { _module.__default.InList(TInt, $Box(x#3), xs#0) } 
      true
         ==> 
        _module.__default.InList(TInt, $Box(x#3), xs#0)
         ==> _module.__default.InList(TInt, $Box(x#3), ys#0));
}



// function declaration for _module._default.length
function _module.__default.length(_module._default.length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType) : int;

function _module.__default.length#canCall(_module._default.length$_T0: Ty, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.length(_module._default.length$_T0, $LS($ly), xs#0) } 
  _module.__default.length(_module._default.length$_T0, $LS($ly), xs#0)
     == _module.__default.length(_module._default.length$_T0, $ly, xs#0));

// fuel synonym axiom
axiom (forall _module._default.length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.length(_module._default.length$_T0, AsFuelBottom($ly), xs#0) } 
  _module.__default.length(_module._default.length$_T0, $ly, xs#0)
     == _module.__default.length(_module._default.length$_T0, $LZ, xs#0));

// consequence axiom for _module.__default.length
axiom 10 <= $FunctionContextHeight
   ==> (forall _module._default.length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.length(_module._default.length$_T0, $ly, xs#0) } 
    _module.__default.length#canCall(_module._default.length$_T0, xs#0)
         || (10 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.length$_T0)))
       ==> LitInt(0) <= _module.__default.length(_module._default.length$_T0, $ly, xs#0));

function _module.__default.length#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.length
axiom (forall _module._default.length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.length#requires(_module._default.length$_T0, $ly, xs#0) } 
  $Is(xs#0, Tclass._module.List(_module._default.length$_T0))
     ==> _module.__default.length#requires(_module._default.length$_T0, $ly, xs#0)
       == true);

// definition axiom for _module.__default.length (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall _module._default.length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.length(_module._default.length$_T0, $LS($ly), xs#0) } 
    _module.__default.length#canCall(_module._default.length$_T0, xs#0)
         || (10 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.length$_T0)))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var tail#1 := _module.List._h2(xs#0); 
            _module.__default.length#canCall(_module._default.length$_T0, tail#1)))
         && _module.__default.length(_module._default.length$_T0, $LS($ly), xs#0)
           == (if _module.List.Nil_q(xs#0)
             then 0
             else (var tail#0 := _module.List._h2(xs#0); 
              1 + _module.__default.length(_module._default.length$_T0, $ly, tail#0))));

// definition axiom for _module.__default.length for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall _module._default.length$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.length(_module._default.length$_T0, $LS($ly), Lit(xs#0)) } 
    _module.__default.length#canCall(_module._default.length$_T0, Lit(xs#0))
         || (10 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.length$_T0)))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var tail#3 := Lit(_module.List._h2(Lit(xs#0))); 
            _module.__default.length#canCall(_module._default.length$_T0, tail#3)))
         && _module.__default.length(_module._default.length$_T0, $LS($ly), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then 0
             else (var tail#2 := Lit(_module.List._h2(Lit(xs#0))); 
              LitInt(1 + _module.__default.length(_module._default.length$_T0, $LS($ly), tail#2)))));

procedure CheckWellformed$$_module.__default.length(_module._default.length$_T0: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.length$_T0)));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.length(_module._default.length$_T0: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function length
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(273,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    if (*)
    {
        assume LitInt(0)
           <= _module.__default.length(_module._default.length$_T0, $LS($LZ), xs#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assert $Is(LitInt(0), Tclass._System.nat());
            assume _module.__default.length(_module._default.length$_T0, $LS($LZ), xs#0)
               == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.length(_module._default.length$_T0, $LS($LZ), xs#0), 
              Tclass._System.nat());
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.length$_T0);
            assume $Is(_mcc#1#0, Tclass._module.List(_module._default.length$_T0));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.List(_module._default.length$_T0));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List(_module._default.length$_T0));
            assume tail#Z#0 == let#0#0#0;
            ##xs#0 := tail#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(_module._default.length$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##xs#0) < DtRank(xs#0);
            assume _module.__default.length#canCall(_module._default.length$_T0, tail#Z#0);
            assert $Is(1 + _module.__default.length(_module._default.length$_T0, $LS($LZ), tail#Z#0), 
              Tclass._System.nat());
            assume _module.__default.length(_module._default.length$_T0, $LS($LZ), xs#0)
               == 1 + _module.__default.length(_module._default.length$_T0, $LS($LZ), tail#Z#0);
            assume _module.__default.length#canCall(_module._default.length$_T0, tail#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.length(_module._default.length$_T0, $LS($LZ), xs#0), 
              Tclass._System.nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.elems
function _module.__default.elems(_module._default.elems$_T0: Ty, $ly: LayerType, xs#0: DatatypeType) : Set Box;

function _module.__default.elems#canCall(_module._default.elems$_T0: Ty, xs#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.elems$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.elems(_module._default.elems$_T0, $LS($ly), xs#0) } 
  _module.__default.elems(_module._default.elems$_T0, $LS($ly), xs#0)
     == _module.__default.elems(_module._default.elems$_T0, $ly, xs#0));

// fuel synonym axiom
axiom (forall _module._default.elems$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.elems(_module._default.elems$_T0, AsFuelBottom($ly), xs#0) } 
  _module.__default.elems(_module._default.elems$_T0, $ly, xs#0)
     == _module.__default.elems(_module._default.elems$_T0, $LZ, xs#0));

// consequence axiom for _module.__default.elems
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.elems$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.elems(_module._default.elems$_T0, $ly, xs#0) } 
    _module.__default.elems#canCall(_module._default.elems$_T0, xs#0)
         || (11 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.elems$_T0)))
       ==> $Is(_module.__default.elems(_module._default.elems$_T0, $ly, xs#0), 
        TSet(_module._default.elems$_T0)));

function _module.__default.elems#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.elems
axiom (forall _module._default.elems$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
  { _module.__default.elems#requires(_module._default.elems$_T0, $ly, xs#0) } 
  $Is(xs#0, Tclass._module.List(_module._default.elems$_T0))
     ==> _module.__default.elems#requires(_module._default.elems$_T0, $ly, xs#0) == true);

// definition axiom for _module.__default.elems (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.elems$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    { _module.__default.elems(_module._default.elems$_T0, $LS($ly), xs#0) } 
    _module.__default.elems#canCall(_module._default.elems$_T0, xs#0)
         || (11 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.elems$_T0)))
       ==> (!_module.List.Nil_q(xs#0)
           ==> (var tail#1 := _module.List._h2(xs#0); 
            _module.__default.elems#canCall(_module._default.elems$_T0, tail#1)))
         && _module.__default.elems(_module._default.elems$_T0, $LS($ly), xs#0)
           == (if _module.List.Nil_q(xs#0)
             then Set#Empty(): Set Box
             else (var tail#0 := _module.List._h2(xs#0); 
              (var x#0 := _module.List._h1(xs#0); 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, x#0), 
                  _module.__default.elems(_module._default.elems$_T0, $ly, tail#0))))));

// definition axiom for _module.__default.elems for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.elems$_T0: Ty, $ly: LayerType, xs#0: DatatypeType :: 
    {:weight 3} { _module.__default.elems(_module._default.elems$_T0, $LS($ly), Lit(xs#0)) } 
    _module.__default.elems#canCall(_module._default.elems$_T0, Lit(xs#0))
         || (11 != $FunctionContextHeight
           && $Is(xs#0, Tclass._module.List(_module._default.elems$_T0)))
       ==> (!Lit(_module.List.Nil_q(Lit(xs#0)))
           ==> (var tail#3 := Lit(_module.List._h2(Lit(xs#0))); 
            _module.__default.elems#canCall(_module._default.elems$_T0, tail#3)))
         && _module.__default.elems(_module._default.elems$_T0, $LS($ly), Lit(xs#0))
           == (if _module.List.Nil_q(Lit(xs#0))
             then Set#Empty(): Set Box
             else (var tail#2 := Lit(_module.List._h2(Lit(xs#0))); 
              (var x#2 := Lit(_module.List._h1(Lit(xs#0))); 
                Set#Union(Set#UnionOne(Set#Empty(): Set Box, x#2), 
                  _module.__default.elems(_module._default.elems$_T0, $LS($ly), tail#2))))));

procedure CheckWellformed$$_module.__default.elems(_module._default.elems$_T0: Ty, 
    xs#0: DatatypeType
       where $Is(xs#0, Tclass._module.List(_module._default.elems$_T0)));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.elems(_module._default.elems$_T0: Ty, xs#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: Box;
  var _mcc#1#0: DatatypeType;
  var tail#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var x#Z#0: Box;
  var let#1#0#0: Box;
  var ##xs#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function elems
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(280,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    if (*)
    {
        assume $Is(_module.__default.elems(_module._default.elems$_T0, $LS($LZ), xs#0), 
          TSet(_module._default.elems$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (xs#0 == #_module.List.Nil())
        {
            assume _module.__default.elems(_module._default.elems$_T0, $LS($LZ), xs#0)
               == Lit(Set#Empty(): Set Box);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.elems(_module._default.elems$_T0, $LS($LZ), xs#0), 
              TSet(_module._default.elems$_T0));
        }
        else if (xs#0 == #_module.List.Cons(_mcc#0#0, _mcc#1#0))
        {
            assume $IsBox(_mcc#0#0, _module._default.elems$_T0);
            assume $Is(_mcc#1#0, Tclass._module.List(_module._default.elems$_T0));
            havoc tail#Z#0;
            assume $Is(tail#Z#0, Tclass._module.List(_module._default.elems$_T0));
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.List(_module._default.elems$_T0));
            assume tail#Z#0 == let#0#0#0;
            havoc x#Z#0;
            assume $IsBox(x#Z#0, _module._default.elems$_T0);
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#1#0#0, _module._default.elems$_T0);
            assume x#Z#0 == let#1#0#0;
            ##xs#0 := tail#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##xs#0, Tclass._module.List(_module._default.elems$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##xs#0) < DtRank(xs#0);
            assume _module.__default.elems#canCall(_module._default.elems$_T0, tail#Z#0);
            assume _module.__default.elems(_module._default.elems$_T0, $LS($LZ), xs#0)
               == Set#Union(Set#UnionOne(Set#Empty(): Set Box, x#Z#0), 
                _module.__default.elems(_module._default.elems$_T0, $LS($LZ), tail#Z#0));
            assume _module.__default.elems#canCall(_module._default.elems$_T0, tail#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.elems(_module._default.elems$_T0, $LS($LZ), xs#0), 
              TSet(_module._default.elems$_T0));
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Card
function _module.__default.Card(_module._default.Card$_T0: Ty, s#0: Set Box) : int;

function _module.__default.Card#canCall(_module._default.Card$_T0: Ty, s#0: Set Box) : bool;

// consequence axiom for _module.__default.Card
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Card$_T0: Ty, s#0: Set Box :: 
    { _module.__default.Card(_module._default.Card$_T0, s#0) } 
    _module.__default.Card#canCall(_module._default.Card$_T0, s#0)
         || (12 != $FunctionContextHeight && $Is(s#0, TSet(_module._default.Card$_T0)))
       ==> LitInt(0) <= _module.__default.Card(_module._default.Card$_T0, s#0));

function _module.__default.Card#requires(Ty, Set Box) : bool;

// #requires axiom for _module.__default.Card
axiom (forall _module._default.Card$_T0: Ty, s#0: Set Box :: 
  { _module.__default.Card#requires(_module._default.Card$_T0, s#0) } 
  $Is(s#0, TSet(_module._default.Card$_T0))
     ==> _module.__default.Card#requires(_module._default.Card$_T0, s#0) == true);

// definition axiom for _module.__default.Card (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Card$_T0: Ty, s#0: Set Box :: 
    { _module.__default.Card(_module._default.Card$_T0, s#0) } 
    _module.__default.Card#canCall(_module._default.Card$_T0, s#0)
         || (12 != $FunctionContextHeight && $Is(s#0, TSet(_module._default.Card$_T0)))
       ==> _module.__default.Card(_module._default.Card$_T0, s#0) == Set#Card(s#0));

// definition axiom for _module.__default.Card for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall _module._default.Card$_T0: Ty, s#0: Set Box :: 
    {:weight 3} { _module.__default.Card(_module._default.Card$_T0, Lit(s#0)) } 
    _module.__default.Card#canCall(_module._default.Card$_T0, Lit(s#0))
         || (12 != $FunctionContextHeight && $Is(s#0, TSet(_module._default.Card$_T0)))
       ==> _module.__default.Card(_module._default.Card$_T0, Lit(s#0))
         == Set#Card(Lit(s#0)));

procedure CheckWellformed$$_module.__default.Card(_module._default.Card$_T0: Ty, 
    s#0: Set Box where $Is(s#0, TSet(_module._default.Card$_T0)));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Card(_module._default.Card$_T0: Ty, s#0: Set Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for function Card
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(287,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    if (*)
    {
        assume LitInt(0) <= _module.__default.Card(_module._default.Card$_T0, s#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert $Is(Set#Card(s#0), Tclass._System.nat());
        assume _module.__default.Card(_module._default.Card$_T0, s#0) == Set#Card(s#0);
        assume true;
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Card(_module._default.Card$_T0, s#0), Tclass._System.nat());
    }
}



// function declaration for _module._default.Identity
function _module.__default.Identity(_module._default.Identity$_T0: Ty, s#0: Set Box) : Set Box;

function _module.__default.Identity#canCall(_module._default.Identity$_T0: Ty, s#0: Set Box) : bool;

// consequence axiom for _module.__default.Identity
axiom 42 <= $FunctionContextHeight
   ==> (forall _module._default.Identity$_T0: Ty, s#0: Set Box :: 
    { _module.__default.Identity(_module._default.Identity$_T0, s#0) } 
    _module.__default.Identity#canCall(_module._default.Identity$_T0, s#0)
         || (42 != $FunctionContextHeight && $Is(s#0, TSet(_module._default.Identity$_T0)))
       ==> $Is(_module.__default.Identity(_module._default.Identity$_T0, s#0), 
        TSet(_module._default.Identity$_T0)));

function _module.__default.Identity#requires(Ty, Set Box) : bool;

// #requires axiom for _module.__default.Identity
axiom (forall _module._default.Identity$_T0: Ty, s#0: Set Box :: 
  { _module.__default.Identity#requires(_module._default.Identity$_T0, s#0) } 
  $Is(s#0, TSet(_module._default.Identity$_T0))
     ==> _module.__default.Identity#requires(_module._default.Identity$_T0, s#0) == true);

// definition axiom for _module.__default.Identity (revealed)
axiom 42 <= $FunctionContextHeight
   ==> (forall _module._default.Identity$_T0: Ty, s#0: Set Box :: 
    { _module.__default.Identity(_module._default.Identity$_T0, s#0) } 
    _module.__default.Identity#canCall(_module._default.Identity$_T0, s#0)
         || (42 != $FunctionContextHeight && $Is(s#0, TSet(_module._default.Identity$_T0)))
       ==> _module.__default.Identity(_module._default.Identity$_T0, s#0) == s#0);

// definition axiom for _module.__default.Identity for all literals (revealed)
axiom 42 <= $FunctionContextHeight
   ==> (forall _module._default.Identity$_T0: Ty, s#0: Set Box :: 
    {:weight 3} { _module.__default.Identity(_module._default.Identity$_T0, Lit(s#0)) } 
    _module.__default.Identity#canCall(_module._default.Identity$_T0, Lit(s#0))
         || (42 != $FunctionContextHeight && $Is(s#0, TSet(_module._default.Identity$_T0)))
       ==> _module.__default.Identity(_module._default.Identity$_T0, Lit(s#0)) == Lit(s#0));

procedure CheckWellformed$$_module.__default.Identity(_module._default.Identity$_T0: Ty, 
    s#0: Set Box where $Is(s#0, TSet(_module._default.Identity$_T0)));
  free requires 42 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.MultisetToSet
function _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0: Ty, $ly: LayerType, m#0: MultiSet Box)
   : Set Box;

function _module.__default.MultisetToSet#canCall(_module._default.MultisetToSet$_T0: Ty, m#0: MultiSet Box) : bool;

// layer synonym axiom
axiom (forall _module._default.MultisetToSet$_T0: Ty, $ly: LayerType, m#0: MultiSet Box :: 
  { _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($ly), m#0) } 
  _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($ly), m#0)
     == _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $ly, m#0));

// fuel synonym axiom
axiom (forall _module._default.MultisetToSet$_T0: Ty, $ly: LayerType, m#0: MultiSet Box :: 
  { _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, AsFuelBottom($ly), m#0) } 
  _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $ly, m#0)
     == _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LZ, m#0));

// consequence axiom for _module.__default.MultisetToSet
axiom 40 <= $FunctionContextHeight
   ==> (forall _module._default.MultisetToSet$_T0: Ty, $ly: LayerType, m#0: MultiSet Box :: 
    { _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $ly, m#0) } 
    _module.__default.MultisetToSet#canCall(_module._default.MultisetToSet$_T0, m#0)
         || (40 != $FunctionContextHeight
           && $Is(m#0, TMultiSet(_module._default.MultisetToSet$_T0)))
       ==> $Is(_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $ly, m#0), 
        TSet(_module._default.MultisetToSet$_T0)));

function _module.__default.MultisetToSet#requires(Ty, LayerType, MultiSet Box) : bool;

// #requires axiom for _module.__default.MultisetToSet
axiom (forall _module._default.MultisetToSet$_T0: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    m#0: MultiSet Box :: 
  { _module.__default.MultisetToSet#requires(_module._default.MultisetToSet$_T0, $ly, m#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && $Is(m#0, TMultiSet(_module._default.MultisetToSet$_T0))
     ==> _module.__default.MultisetToSet#requires(_module._default.MultisetToSet$_T0, $ly, m#0)
       == true);

function $let#0_x(_module._default.MultisetToSet$_T0: Ty, m: MultiSet Box) : Box;

function $let#0$canCall(_module._default.MultisetToSet$_T0: Ty, m: MultiSet Box) : bool;

axiom (forall _module._default.MultisetToSet$_T0: Ty, m: MultiSet Box :: 
  { $let#0_x(_module._default.MultisetToSet$_T0, m) } 
  $let#0$canCall(_module._default.MultisetToSet$_T0, m)
     ==> m[$let#0_x(_module._default.MultisetToSet$_T0, m)] > 0);

// definition axiom for _module.__default.MultisetToSet (revealed)
axiom 40 <= $FunctionContextHeight
   ==> (forall _module._default.MultisetToSet$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      m#0: MultiSet Box :: 
    { _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($ly), m#0), $IsGoodHeap($Heap) } 
    _module.__default.MultisetToSet#canCall(_module._default.MultisetToSet$_T0, m#0)
         || (40 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(m#0, TMultiSet(_module._default.MultisetToSet$_T0)))
       ==> (MultiSet#Card(m#0) != LitInt(0)
           ==> $let#0$canCall(_module._default.MultisetToSet$_T0, m#0)
             && _module.__default.MultisetToSet#canCall(_module._default.MultisetToSet$_T0, 
              MultiSet#Difference(m#0, 
                MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, 
                  $let#0_x(_module._default.MultisetToSet$_T0, m#0)))))
         && _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($ly), m#0)
           == (if MultiSet#Card(m#0) == LitInt(0)
             then Set#Empty(): Set Box
             else (var x#0 := $let#0_x(_module._default.MultisetToSet$_T0, m#0); 
              Set#Union(_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, 
                  $ly, 
                  MultiSet#Difference(m#0, MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, x#0))), 
                Set#UnionOne(Set#Empty(): Set Box, x#0)))));

// definition axiom for _module.__default.MultisetToSet for all literals (revealed)
axiom 40 <= $FunctionContextHeight
   ==> (forall _module._default.MultisetToSet$_T0: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      m#0: MultiSet Box :: 
    {:weight 3} { _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($ly), Lit(m#0)), $IsGoodHeap($Heap) } 
    _module.__default.MultisetToSet#canCall(_module._default.MultisetToSet$_T0, Lit(m#0))
         || (40 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(m#0, TMultiSet(_module._default.MultisetToSet$_T0)))
       ==> (MultiSet#Card(Lit(m#0)) != LitInt(0)
           ==> $let#0$canCall(_module._default.MultisetToSet$_T0, Lit(m#0))
             && _module.__default.MultisetToSet#canCall(_module._default.MultisetToSet$_T0, 
              MultiSet#Difference(m#0, 
                MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, 
                  $let#0_x(_module._default.MultisetToSet$_T0, Lit(m#0))))))
         && _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($ly), Lit(m#0))
           == (if MultiSet#Card(Lit(m#0)) == LitInt(0)
             then Set#Empty(): Set Box
             else (var x#1 := $let#0_x(_module._default.MultisetToSet$_T0, Lit(m#0)); 
              Set#Union(_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, 
                  $LS($ly), 
                  MultiSet#Difference(m#0, MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, x#1))), 
                Set#UnionOne(Set#Empty(): Set Box, x#1)))));

procedure CheckWellformed$$_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0: Ty, 
    m#0: MultiSet Box where $Is(m#0, TMultiSet(_module._default.MultisetToSet$_T0)));
  free requires 40 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0: Ty, m#0: MultiSet Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#2: Box;
  var ##m#0: MultiSet Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function MultisetToSet
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(297,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    if (*)
    {
        assume $Is(_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($LZ), m#0), 
          TSet(_module._default.MultisetToSet$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (MultiSet#Card(m#0) == LitInt(0))
        {
            assume _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($LZ), m#0)
               == Lit(Set#Empty(): Set Box);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($LZ), m#0), 
              TSet(_module._default.MultisetToSet$_T0));
        }
        else
        {
            havoc x#2;
            if ($IsBox(x#2, _module._default.MultisetToSet$_T0))
            {
            }

            assert (exists x#3: Box :: 
              $IsBox(x#3, _module._default.MultisetToSet$_T0) && m#0[x#3] > 0);
            assume $IsBox(x#2, _module._default.MultisetToSet$_T0);
            assume m#0[x#2] > 0;
            ##m#0 := MultiSet#Difference(m#0, MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, x#2));
            // assume allocatedness for argument to function
            assume $IsAlloc(##m#0, TMultiSet(_module._default.MultisetToSet$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert MultiSet#Subset(##m#0, m#0) && !MultiSet#Equal(##m#0, m#0);
            assume _module.__default.MultisetToSet#canCall(_module._default.MultisetToSet$_T0, 
              MultiSet#Difference(m#0, MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, x#2)));
            assume $let#0$canCall(_module._default.MultisetToSet$_T0, m#0);
            assume _module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($LZ), m#0)
               == Set#Union(_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, 
                  $LS($LZ), 
                  MultiSet#Difference(m#0, MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, x#2))), 
                Set#UnionOne(Set#Empty(): Set Box, x#2));
            assume _module.__default.MultisetToSet#canCall(_module._default.MultisetToSet$_T0, 
              MultiSet#Difference(m#0, MultiSet#UnionOne(MultiSet#Empty(): MultiSet Box, x#2)));
            // CheckWellformedWithResult: Let expression
            assume $Is(_module.__default.MultisetToSet(_module._default.MultisetToSet$_T0, $LS($LZ), m#0), 
              TSet(_module._default.MultisetToSet$_T0));
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.SeqToSet
function _module.__default.SeqToSet(_module._default.SeqToSet$_T0: Ty, $ly: LayerType, q#0: Seq Box) : Set Box;

function _module.__default.SeqToSet#canCall(_module._default.SeqToSet$_T0: Ty, q#0: Seq Box) : bool;

// layer synonym axiom
axiom (forall _module._default.SeqToSet$_T0: Ty, $ly: LayerType, q#0: Seq Box :: 
  { _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($ly), q#0) } 
  _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($ly), q#0)
     == _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $ly, q#0));

// fuel synonym axiom
axiom (forall _module._default.SeqToSet$_T0: Ty, $ly: LayerType, q#0: Seq Box :: 
  { _module.__default.SeqToSet(_module._default.SeqToSet$_T0, AsFuelBottom($ly), q#0) } 
  _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $ly, q#0)
     == _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LZ, q#0));

// consequence axiom for _module.__default.SeqToSet
axiom 41 <= $FunctionContextHeight
   ==> (forall _module._default.SeqToSet$_T0: Ty, $ly: LayerType, q#0: Seq Box :: 
    { _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $ly, q#0) } 
    _module.__default.SeqToSet#canCall(_module._default.SeqToSet$_T0, q#0)
         || (41 != $FunctionContextHeight && $Is(q#0, TSeq(_module._default.SeqToSet$_T0)))
       ==> $Is(_module.__default.SeqToSet(_module._default.SeqToSet$_T0, $ly, q#0), 
        TSet(_module._default.SeqToSet$_T0)));

function _module.__default.SeqToSet#requires(Ty, LayerType, Seq Box) : bool;

// #requires axiom for _module.__default.SeqToSet
axiom (forall _module._default.SeqToSet$_T0: Ty, $ly: LayerType, q#0: Seq Box :: 
  { _module.__default.SeqToSet#requires(_module._default.SeqToSet$_T0, $ly, q#0) } 
  $Is(q#0, TSeq(_module._default.SeqToSet$_T0))
     ==> _module.__default.SeqToSet#requires(_module._default.SeqToSet$_T0, $ly, q#0)
       == true);

// definition axiom for _module.__default.SeqToSet (revealed)
axiom 41 <= $FunctionContextHeight
   ==> (forall _module._default.SeqToSet$_T0: Ty, $ly: LayerType, q#0: Seq Box :: 
    { _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($ly), q#0) } 
    _module.__default.SeqToSet#canCall(_module._default.SeqToSet$_T0, q#0)
         || (41 != $FunctionContextHeight && $Is(q#0, TSeq(_module._default.SeqToSet$_T0)))
       ==> (!Seq#Equal(q#0, Seq#Empty(): Seq Box)
           ==> _module.__default.SeqToSet#canCall(_module._default.SeqToSet$_T0, Seq#Drop(q#0, LitInt(1))))
         && _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($ly), q#0)
           == (if Seq#Equal(q#0, Seq#Empty(): Seq Box)
             then Set#Empty(): Set Box
             else Set#Union(Set#UnionOne(Set#Empty(): Set Box, Seq#Index(q#0, LitInt(0))), 
              _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $ly, Seq#Drop(q#0, LitInt(1))))));

// definition axiom for _module.__default.SeqToSet for all literals (revealed)
axiom 41 <= $FunctionContextHeight
   ==> (forall _module._default.SeqToSet$_T0: Ty, $ly: LayerType, q#0: Seq Box :: 
    {:weight 3} { _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($ly), Lit(q#0)) } 
    _module.__default.SeqToSet#canCall(_module._default.SeqToSet$_T0, Lit(q#0))
         || (41 != $FunctionContextHeight && $Is(q#0, TSeq(_module._default.SeqToSet$_T0)))
       ==> (!Seq#Equal(q#0, Seq#Empty(): Seq Box)
           ==> _module.__default.SeqToSet#canCall(_module._default.SeqToSet$_T0, Lit(Seq#Drop(Lit(q#0), LitInt(1)))))
         && _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($ly), Lit(q#0))
           == (if Seq#Equal(q#0, Seq#Empty(): Seq Box)
             then Set#Empty(): Set Box
             else Set#Union(Set#UnionOne(Set#Empty(): Set Box, Seq#Index(Lit(q#0), LitInt(0))), 
              _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($ly), Lit(Seq#Drop(Lit(q#0), LitInt(1)))))));

procedure CheckWellformed$$_module.__default.SeqToSet(_module._default.SeqToSet$_T0: Ty, 
    q#0: Seq Box where $Is(q#0, TSeq(_module._default.SeqToSet$_T0)));
  free requires 41 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.SeqToSet(_module._default.SeqToSet$_T0: Ty, q#0: Seq Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##q#0: Seq Box;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function SeqToSet
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(303,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    if (*)
    {
        assume $Is(_module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($LZ), q#0), 
          TSet(_module._default.SeqToSet$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (Seq#Equal(q#0, Seq#Empty(): Seq Box))
        {
            assume _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($LZ), q#0)
               == Lit(Set#Empty(): Set Box);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($LZ), q#0), 
              TSet(_module._default.SeqToSet$_T0));
        }
        else
        {
            assert 0 <= LitInt(0) && LitInt(0) < Seq#Length(q#0);
            assert 0 <= LitInt(1) && LitInt(1) <= Seq#Length(q#0);
            ##q#0 := Seq#Drop(q#0, LitInt(1));
            // assume allocatedness for argument to function
            assume $IsAlloc(##q#0, TSeq(_module._default.SeqToSet$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert Seq#Rank(##q#0) < Seq#Rank(q#0);
            assume _module.__default.SeqToSet#canCall(_module._default.SeqToSet$_T0, Seq#Drop(q#0, LitInt(1)));
            assume _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($LZ), q#0)
               == Set#Union(Set#UnionOne(Set#Empty(): Set Box, Seq#Index(q#0, LitInt(0))), 
                _module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($LZ), Seq#Drop(q#0, LitInt(1))));
            assume _module.__default.SeqToSet#canCall(_module._default.SeqToSet$_T0, Seq#Drop(q#0, LitInt(1)));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.SeqToSet(_module._default.SeqToSet$_T0, $LS($LZ), q#0), 
              TSet(_module._default.SeqToSet$_T0));
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.IdentityMap(_module._default.IdentityMap$_T0: Ty, 
    _module._default.IdentityMap$_T1: Ty, 
    s#0: Set Box
       where $Is(s#0, 
          TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)))
         && $IsAlloc(s#0, 
          TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)), 
          $Heap))
   returns (m#0: Map Box Box
       where $Is(m#0, TMap(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1))
         && $IsAlloc(m#0, 
          TMap(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1), 
          $Heap));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.IdentityMap(_module._default.IdentityMap$_T0: Ty, 
    _module._default.IdentityMap$_T1: Ty, 
    s#0: Set Box
       where $Is(s#0, 
          TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)))
         && $IsAlloc(s#0, 
          TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)), 
          $Heap))
   returns (m#0: Map Box Box
       where $Is(m#0, TMap(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1))
         && $IsAlloc(m#0, 
          TMap(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1), 
          $Heap));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.IdentityMap(_module._default.IdentityMap$_T0: Ty, 
    _module._default.IdentityMap$_T1: Ty, 
    s#0: Set Box
       where $Is(s#0, 
          TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)))
         && $IsAlloc(s#0, 
          TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)), 
          $Heap))
   returns (m#0: Map Box Box
       where $Is(m#0, TMap(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1))
         && $IsAlloc(m#0, 
          TMap(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1), 
          $Heap), 
    $_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.IdentityMap(_module._default.IdentityMap$_T0: Ty, 
    _module._default.IdentityMap$_T1: Ty, 
    s#0: Set Box)
   returns (m#0: Map Box Box, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#1: Set Box
     where $Is(s#1, 
        TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)))
       && $IsAlloc(s#1, 
        TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)), 
        $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: Set Box;
  var $w$loop#0: bool;
  var $decr$loop#00: Set Box;
  var defass#p#0_0: bool;
  var p#0_0: DatatypeType
     where defass#p#0_0
       ==> $Is(p#0_0, 
          Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1))
         && $IsAlloc(p#0_0, 
          Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1), 
          $Heap);
  var p#0_1: DatatypeType;
  var $rhs#0_0: Map Box Box
     where $Is($rhs#0_0, 
      TMap(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1));
  var $rhs#0_1: Set Box
     where $Is($rhs#0_1, 
      TSet(Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1)));

    // AddMethodImpl: IdentityMap, Impl$$_module.__default.IdentityMap
    // initialize fuel constant
    assume StartFuel_ParseGenerics._default.Many
       == $LS(BaseFuel_ParseGenerics._default.Many);
    assume StartFuelAssert_ParseGenerics._default.Many
       == $LS($LS(BaseFuel_ParseGenerics._default.Many));
    assume AsFuelBottom(BaseFuel_ParseGenerics._default.Many)
       == BaseFuel_ParseGenerics._default.Many;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(311,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(312,5)
    assume true;
    assume true;
    m#0 := Lit(Map#Empty(): Map Box Box);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(312,12)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(313,9)
    assume true;
    assume true;
    s#1 := s#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(313,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(314,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := s#1;
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
      free invariant Set#Subset(s#1, $decr_init$loop#00)
         && (Set#Equal(s#1, $decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(314,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (Set#Equal(s#1, Set#Empty(): Set Box))
        {
            break;
        }

        $decr$loop#00 := s#1;
        // ----- assign-such-that statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(317,11)
        havoc p#0_1;
        if ($Is(p#0_1, 
            Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1))
           && $IsAlloc(p#0_1, 
            Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1), 
            $Heap))
        {
            assume true;
        }

        assert (exists $as#p0_0#0_0: DatatypeType :: 
          $Is($as#p0_0#0_0, 
              Tclass._module.Pair(_module._default.IdentityMap$_T0, _module._default.IdentityMap$_T1))
             && s#1[$Box($as#p0_0#0_0)]);
        defass#p#0_0 := true;
        havoc p#0_0;
        assume s#1[$Box(p#0_0)];
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(317,19)"} true;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(318,10)
        assume true;
        assume true;
        assert defass#p#0_0;
        assume _module.Pair.MkPair_q(p#0_0);
        assert defass#p#0_0;
        assume _module.Pair.MkPair_q(p#0_0);
        assume _module.Pair.MkPair_q(p#0_0) && _module.Pair.MkPair_q(p#0_0);
        $rhs#0_0 := Map#Build(m#0, _module.Pair._0(p#0_0), _module.Pair._1(p#0_0));
        assert defass#p#0_0;
        assume true;
        $rhs#0_1 := Set#Difference(s#1, Set#UnionOne(Set#Empty(): Set Box, $Box(p#0_0)));
        m#0 := $rhs#0_0;
        s#1 := $rhs#0_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(318,34)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/TypeParameters.dfy(314,3)
        assert Set#Subset(s#1, $decr$loop#00) && !Set#Subset($decr$loop#00, s#1);
    }
}



// Constructor function declaration
function #OneLayer.wrap.Wrap(Box) : DatatypeType;

const unique ##OneLayer.wrap.Wrap: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: Box :: 
  { #OneLayer.wrap.Wrap(a#0#0#0) } 
  DatatypeCtorId(#OneLayer.wrap.Wrap(a#0#0#0)) == ##OneLayer.wrap.Wrap);

function OneLayer.wrap.Wrap_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { OneLayer.wrap.Wrap_q(d) } 
  OneLayer.wrap.Wrap_q(d) <==> DatatypeCtorId(d) == ##OneLayer.wrap.Wrap);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { OneLayer.wrap.Wrap_q(d) } 
  OneLayer.wrap.Wrap_q(d)
     ==> (exists a#1#0#0: Box :: d == #OneLayer.wrap.Wrap(a#1#0#0)));

function Tclass.OneLayer.wrap(Ty) : Ty;

const unique Tagclass.OneLayer.wrap: TyTag;

// Tclass.OneLayer.wrap Tag
axiom (forall OneLayer.wrap$V: Ty :: 
  { Tclass.OneLayer.wrap(OneLayer.wrap$V) } 
  Tag(Tclass.OneLayer.wrap(OneLayer.wrap$V)) == Tagclass.OneLayer.wrap
     && TagFamily(Tclass.OneLayer.wrap(OneLayer.wrap$V)) == tytagFamily$wrap);

// Tclass.OneLayer.wrap injectivity 0
axiom (forall OneLayer.wrap$V: Ty :: 
  { Tclass.OneLayer.wrap(OneLayer.wrap$V) } 
  Tclass.OneLayer.wrap_0(Tclass.OneLayer.wrap(OneLayer.wrap$V)) == OneLayer.wrap$V);

function Tclass.OneLayer.wrap_0(Ty) : Ty;

// Box/unbox axiom for Tclass.OneLayer.wrap
axiom (forall OneLayer.wrap$V: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.OneLayer.wrap(OneLayer.wrap$V)) } 
  $IsBox(bx, Tclass.OneLayer.wrap(OneLayer.wrap$V))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.OneLayer.wrap(OneLayer.wrap$V)));

// Constructor $Is
axiom (forall OneLayer.wrap$V: Ty, a#2#0#0: Box :: 
  { $Is(#OneLayer.wrap.Wrap(a#2#0#0), Tclass.OneLayer.wrap(OneLayer.wrap$V)) } 
  $Is(#OneLayer.wrap.Wrap(a#2#0#0), Tclass.OneLayer.wrap(OneLayer.wrap$V))
     <==> $IsBox(a#2#0#0, OneLayer.wrap$V));

// Constructor $IsAlloc
axiom (forall OneLayer.wrap$V: Ty, a#3#0#0: Box, $h: Heap :: 
  { $IsAlloc(#OneLayer.wrap.Wrap(a#3#0#0), Tclass.OneLayer.wrap(OneLayer.wrap$V), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#OneLayer.wrap.Wrap(a#3#0#0), Tclass.OneLayer.wrap(OneLayer.wrap$V), $h)
       <==> $IsAllocBox(a#3#0#0, OneLayer.wrap$V, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, OneLayer.wrap$V: Ty, $h: Heap :: 
  { $IsAllocBox(OneLayer.wrap._h0(d), OneLayer.wrap$V, $h) } 
  $IsGoodHeap($h)
       && 
      OneLayer.wrap.Wrap_q(d)
       && $IsAlloc(d, Tclass.OneLayer.wrap(OneLayer.wrap$V), $h)
     ==> $IsAllocBox(OneLayer.wrap._h0(d), OneLayer.wrap$V, $h));

// Constructor literal
axiom (forall a#4#0#0: Box :: 
  { #OneLayer.wrap.Wrap(Lit(a#4#0#0)) } 
  #OneLayer.wrap.Wrap(Lit(a#4#0#0)) == Lit(#OneLayer.wrap.Wrap(a#4#0#0)));

function OneLayer.wrap._h0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#5#0#0: Box :: 
  { #OneLayer.wrap.Wrap(a#5#0#0) } 
  OneLayer.wrap._h0(#OneLayer.wrap.Wrap(a#5#0#0)) == a#5#0#0);

// Inductive rank
axiom (forall a#6#0#0: Box :: 
  { #OneLayer.wrap.Wrap(a#6#0#0) } 
  BoxRank(a#6#0#0) < DtRank(#OneLayer.wrap.Wrap(a#6#0#0)));

// Depth-one case-split function
function $IsA#OneLayer.wrap(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#OneLayer.wrap(d) } 
  $IsA#OneLayer.wrap(d) ==> OneLayer.wrap.Wrap_q(d));

// Questionmark data type disjunctivity
axiom (forall OneLayer.wrap$V: Ty, d: DatatypeType :: 
  { OneLayer.wrap.Wrap_q(d), $Is(d, Tclass.OneLayer.wrap(OneLayer.wrap$V)) } 
  $Is(d, Tclass.OneLayer.wrap(OneLayer.wrap$V)) ==> OneLayer.wrap.Wrap_q(d));

// Datatype extensional equality declaration
function OneLayer.wrap#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #OneLayer.wrap.Wrap
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { OneLayer.wrap#Equal(a, b) } 
  true
     ==> (OneLayer.wrap#Equal(a, b) <==> OneLayer.wrap._h0(a) == OneLayer.wrap._h0(b)));

// Datatype extensionality axiom: OneLayer.wrap
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { OneLayer.wrap#Equal(a, b) } 
  OneLayer.wrap#Equal(a, b) <==> a == b);

const unique class.OneLayer.wrap: ClassName;

const unique class.OneLayer.__default: ClassName;

function Tclass.OneLayer.__default() : Ty;

const unique Tagclass.OneLayer.__default: TyTag;

// Tclass.OneLayer.__default Tag
axiom Tag(Tclass.OneLayer.__default()) == Tagclass.OneLayer.__default
   && TagFamily(Tclass.OneLayer.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.OneLayer.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.OneLayer.__default()) } 
  $IsBox(bx, Tclass.OneLayer.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.OneLayer.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.OneLayer.__default()) } 
  $Is($o, Tclass.OneLayer.__default())
     <==> $o == null || dtype($o) == Tclass.OneLayer.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.OneLayer.__default(), $h) } 
  $IsAlloc($o, Tclass.OneLayer.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// Constructor function declaration
function #TwoLayers.wrap2.Wrap2(DatatypeType) : DatatypeType;

const unique ##TwoLayers.wrap2.Wrap2: DtCtorId;

// Constructor identifier
axiom (forall a#7#0#0: DatatypeType :: 
  { #TwoLayers.wrap2.Wrap2(a#7#0#0) } 
  DatatypeCtorId(#TwoLayers.wrap2.Wrap2(a#7#0#0)) == ##TwoLayers.wrap2.Wrap2);

function TwoLayers.wrap2.Wrap2_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TwoLayers.wrap2.Wrap2_q(d) } 
  TwoLayers.wrap2.Wrap2_q(d) <==> DatatypeCtorId(d) == ##TwoLayers.wrap2.Wrap2);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TwoLayers.wrap2.Wrap2_q(d) } 
  TwoLayers.wrap2.Wrap2_q(d)
     ==> (exists a#8#0#0: DatatypeType :: d == #TwoLayers.wrap2.Wrap2(a#8#0#0)));

function Tclass.TwoLayers.wrap2(Ty) : Ty;

const unique Tagclass.TwoLayers.wrap2: TyTag;

// Tclass.TwoLayers.wrap2 Tag
axiom (forall TwoLayers.wrap2$T: Ty :: 
  { Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T) } 
  Tag(Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T)) == Tagclass.TwoLayers.wrap2
     && TagFamily(Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T)) == tytagFamily$wrap2);

// Tclass.TwoLayers.wrap2 injectivity 0
axiom (forall TwoLayers.wrap2$T: Ty :: 
  { Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T) } 
  Tclass.TwoLayers.wrap2_0(Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T))
     == TwoLayers.wrap2$T);

function Tclass.TwoLayers.wrap2_0(Ty) : Ty;

// Box/unbox axiom for Tclass.TwoLayers.wrap2
axiom (forall TwoLayers.wrap2$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T)) } 
  $IsBox(bx, Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T)));

// Constructor $Is
axiom (forall TwoLayers.wrap2$T: Ty, a#9#0#0: DatatypeType :: 
  { $Is(#TwoLayers.wrap2.Wrap2(a#9#0#0), Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T)) } 
  $Is(#TwoLayers.wrap2.Wrap2(a#9#0#0), Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T))
     <==> $Is(a#9#0#0, Tclass.OneLayer.wrap(TwoLayers.wrap2$T)));

// Constructor $IsAlloc
axiom (forall TwoLayers.wrap2$T: Ty, a#10#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#TwoLayers.wrap2.Wrap2(a#10#0#0), Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TwoLayers.wrap2.Wrap2(a#10#0#0), Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T), $h)
       <==> $IsAlloc(a#10#0#0, Tclass.OneLayer.wrap(TwoLayers.wrap2$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, TwoLayers.wrap2$T: Ty, $h: Heap :: 
  { $IsAlloc(TwoLayers.wrap2.get(d), Tclass.OneLayer.wrap(TwoLayers.wrap2$T), $h) } 
  $IsGoodHeap($h)
       && 
      TwoLayers.wrap2.Wrap2_q(d)
       && $IsAlloc(d, Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T), $h)
     ==> $IsAlloc(TwoLayers.wrap2.get(d), Tclass.OneLayer.wrap(TwoLayers.wrap2$T), $h));

// Constructor literal
axiom (forall a#11#0#0: DatatypeType :: 
  { #TwoLayers.wrap2.Wrap2(Lit(a#11#0#0)) } 
  #TwoLayers.wrap2.Wrap2(Lit(a#11#0#0)) == Lit(#TwoLayers.wrap2.Wrap2(a#11#0#0)));

function TwoLayers.wrap2.get(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: DatatypeType :: 
  { #TwoLayers.wrap2.Wrap2(a#12#0#0) } 
  TwoLayers.wrap2.get(#TwoLayers.wrap2.Wrap2(a#12#0#0)) == a#12#0#0);

// Inductive rank
axiom (forall a#13#0#0: DatatypeType :: 
  { #TwoLayers.wrap2.Wrap2(a#13#0#0) } 
  DtRank(a#13#0#0) < DtRank(#TwoLayers.wrap2.Wrap2(a#13#0#0)));

// Depth-one case-split function
function $IsA#TwoLayers.wrap2(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#TwoLayers.wrap2(d) } 
  $IsA#TwoLayers.wrap2(d) ==> TwoLayers.wrap2.Wrap2_q(d));

// Questionmark data type disjunctivity
axiom (forall TwoLayers.wrap2$T: Ty, d: DatatypeType :: 
  { TwoLayers.wrap2.Wrap2_q(d), $Is(d, Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T)) } 
  $Is(d, Tclass.TwoLayers.wrap2(TwoLayers.wrap2$T)) ==> TwoLayers.wrap2.Wrap2_q(d));

// Datatype extensional equality declaration
function TwoLayers.wrap2#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #TwoLayers.wrap2.Wrap2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TwoLayers.wrap2#Equal(a, b) } 
  true
     ==> (TwoLayers.wrap2#Equal(a, b)
       <==> OneLayer.wrap#Equal(TwoLayers.wrap2.get(a), TwoLayers.wrap2.get(b))));

// Datatype extensionality axiom: TwoLayers.wrap2
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TwoLayers.wrap2#Equal(a, b) } 
  TwoLayers.wrap2#Equal(a, b) <==> a == b);

const unique class.TwoLayers.wrap2: ClassName;

const unique class.TwoLayers.__default: ClassName;

function Tclass.TwoLayers.__default() : Ty;

const unique Tagclass.TwoLayers.__default: TyTag;

// Tclass.TwoLayers.__default Tag
axiom Tag(Tclass.TwoLayers.__default()) == Tagclass.TwoLayers.__default
   && TagFamily(Tclass.TwoLayers.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.TwoLayers.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TwoLayers.__default()) } 
  $IsBox(bx, Tclass.TwoLayers.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TwoLayers.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TwoLayers.__default()) } 
  $Is($o, Tclass.TwoLayers.__default())
     <==> $o == null || dtype($o) == Tclass.TwoLayers.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TwoLayers.__default(), $h) } 
  $IsAlloc($o, Tclass.TwoLayers.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for TwoLayers._default.F
function TwoLayers.__default.F(TwoLayers._default.F$U: Ty, w#0: DatatypeType) : DatatypeType;

function TwoLayers.__default.F#canCall(TwoLayers._default.F$U: Ty, w#0: DatatypeType) : bool;

// consequence axiom for TwoLayers.__default.F
axiom true
   ==> (forall TwoLayers._default.F$U: Ty, w#0: DatatypeType :: 
    { TwoLayers.__default.F(TwoLayers._default.F$U, w#0) } 
    TwoLayers.__default.F#canCall(TwoLayers._default.F$U, w#0)
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.F$U))
       ==> $Is(TwoLayers.__default.F(TwoLayers._default.F$U, w#0), 
        Tclass.OneLayer.wrap(TwoLayers._default.F$U)));

function TwoLayers.__default.F#requires(Ty, DatatypeType) : bool;

// #requires axiom for TwoLayers.__default.F
axiom (forall TwoLayers._default.F$U: Ty, w#0: DatatypeType :: 
  { TwoLayers.__default.F#requires(TwoLayers._default.F$U, w#0) } 
  $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.F$U))
     ==> TwoLayers.__default.F#requires(TwoLayers._default.F$U, w#0) == true);

// definition axiom for TwoLayers.__default.F (revealed)
axiom true
   ==> (forall TwoLayers._default.F$U: Ty, w#0: DatatypeType :: 
    { TwoLayers.__default.F(TwoLayers._default.F$U, w#0) } 
    TwoLayers.__default.F#canCall(TwoLayers._default.F$U, w#0)
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.F$U))
       ==> TwoLayers.wrap2.Wrap2_q(w#0)
         && TwoLayers.__default.F(TwoLayers._default.F$U, w#0)
           == (var a#4 := TwoLayers.wrap2.get(w#0); a#4));

// definition axiom for TwoLayers.__default.F for all literals (revealed)
axiom true
   ==> (forall TwoLayers._default.F$U: Ty, w#0: DatatypeType :: 
    {:weight 3} { TwoLayers.__default.F(TwoLayers._default.F$U, Lit(w#0)) } 
    TwoLayers.__default.F#canCall(TwoLayers._default.F$U, Lit(w#0))
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.F$U))
       ==> TwoLayers.wrap2.Wrap2_q(Lit(w#0))
         && TwoLayers.__default.F(TwoLayers._default.F$U, Lit(w#0))
           == (var a#6 := Lit(TwoLayers.wrap2.get(Lit(w#0))); a#6));

// function declaration for TwoLayers._default.G
function TwoLayers.__default.G(TwoLayers._default.G$U: Ty, w#0: DatatypeType) : DatatypeType;

function TwoLayers.__default.G#canCall(TwoLayers._default.G$U: Ty, w#0: DatatypeType) : bool;

// consequence axiom for TwoLayers.__default.G
axiom true
   ==> (forall TwoLayers._default.G$U: Ty, w#0: DatatypeType :: 
    { TwoLayers.__default.G(TwoLayers._default.G$U, w#0) } 
    TwoLayers.__default.G#canCall(TwoLayers._default.G$U, w#0)
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.G$U))
       ==> $Is(TwoLayers.__default.G(TwoLayers._default.G$U, w#0), 
        Tclass.OneLayer.wrap(TwoLayers._default.G$U)));

function TwoLayers.__default.G#requires(Ty, DatatypeType) : bool;

// #requires axiom for TwoLayers.__default.G
axiom (forall TwoLayers._default.G$U: Ty, w#0: DatatypeType :: 
  { TwoLayers.__default.G#requires(TwoLayers._default.G$U, w#0) } 
  $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.G$U))
     ==> TwoLayers.__default.G#requires(TwoLayers._default.G$U, w#0) == true);

// definition axiom for TwoLayers.__default.G (revealed)
axiom true
   ==> (forall TwoLayers._default.G$U: Ty, w#0: DatatypeType :: 
    { TwoLayers.__default.G(TwoLayers._default.G$U, w#0) } 
    TwoLayers.__default.G#canCall(TwoLayers._default.G$U, w#0)
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.G$U))
       ==> TwoLayers.wrap2.Wrap2_q(w#0)
         && TwoLayers.wrap2.Wrap2_q(w#0)
         && TwoLayers.__default.G(TwoLayers._default.G$U, w#0)
           == (var a#4 := TwoLayers.wrap2.get(w#0); TwoLayers.wrap2.get(w#0)));

// definition axiom for TwoLayers.__default.G for all literals (revealed)
axiom true
   ==> (forall TwoLayers._default.G$U: Ty, w#0: DatatypeType :: 
    {:weight 3} { TwoLayers.__default.G(TwoLayers._default.G$U, Lit(w#0)) } 
    TwoLayers.__default.G#canCall(TwoLayers._default.G$U, Lit(w#0))
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.G$U))
       ==> TwoLayers.wrap2.Wrap2_q(Lit(w#0))
         && TwoLayers.wrap2.Wrap2_q(Lit(w#0))
         && TwoLayers.__default.G(TwoLayers._default.G$U, Lit(w#0))
           == (var a#6 := Lit(TwoLayers.wrap2.get(Lit(w#0))); 
            Lit(TwoLayers.wrap2.get(Lit(w#0)))));

// function declaration for TwoLayers._default.H
function TwoLayers.__default.H(TwoLayers._default.H$U: Ty, w#0: DatatypeType) : DatatypeType;

function TwoLayers.__default.H#canCall(TwoLayers._default.H$U: Ty, w#0: DatatypeType) : bool;

// consequence axiom for TwoLayers.__default.H
axiom true
   ==> (forall TwoLayers._default.H$U: Ty, w#0: DatatypeType :: 
    { TwoLayers.__default.H(TwoLayers._default.H$U, w#0) } 
    TwoLayers.__default.H#canCall(TwoLayers._default.H$U, w#0)
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.H$U))
       ==> $Is(TwoLayers.__default.H(TwoLayers._default.H$U, w#0), 
        Tclass.OneLayer.wrap(TwoLayers._default.H$U)));

function TwoLayers.__default.H#requires(Ty, DatatypeType) : bool;

// #requires axiom for TwoLayers.__default.H
axiom (forall TwoLayers._default.H$U: Ty, w#0: DatatypeType :: 
  { TwoLayers.__default.H#requires(TwoLayers._default.H$U, w#0) } 
  $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.H$U))
     ==> TwoLayers.__default.H#requires(TwoLayers._default.H$U, w#0) == true);

// definition axiom for TwoLayers.__default.H (revealed)
axiom true
   ==> (forall TwoLayers._default.H$U: Ty, w#0: DatatypeType :: 
    { TwoLayers.__default.H(TwoLayers._default.H$U, w#0) } 
    TwoLayers.__default.H#canCall(TwoLayers._default.H$U, w#0)
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.H$U))
       ==> TwoLayers.wrap2.Wrap2_q(w#0)
         && TwoLayers.__default.H(TwoLayers._default.H$U, w#0) == TwoLayers.wrap2.get(w#0));

// definition axiom for TwoLayers.__default.H for all literals (revealed)
axiom true
   ==> (forall TwoLayers._default.H$U: Ty, w#0: DatatypeType :: 
    {:weight 3} { TwoLayers.__default.H(TwoLayers._default.H$U, Lit(w#0)) } 
    TwoLayers.__default.H#canCall(TwoLayers._default.H$U, Lit(w#0))
         || $Is(w#0, Tclass.TwoLayers.wrap2(TwoLayers._default.H$U))
       ==> TwoLayers.wrap2.Wrap2_q(Lit(w#0))
         && TwoLayers.__default.H(TwoLayers._default.H$U, Lit(w#0))
           == Lit(TwoLayers.wrap2.get(Lit(w#0))));

// Constructor function declaration
function #ArrayTypeMagic.ArrayCubeTree.Leaf(ref) : DatatypeType;

const unique ##ArrayTypeMagic.ArrayCubeTree.Leaf: DtCtorId;

// Constructor identifier
axiom (forall a#0#0#0: ref :: 
  { #ArrayTypeMagic.ArrayCubeTree.Leaf(a#0#0#0) } 
  DatatypeCtorId(#ArrayTypeMagic.ArrayCubeTree.Leaf(a#0#0#0))
     == ##ArrayTypeMagic.ArrayCubeTree.Leaf);

function ArrayTypeMagic.ArrayCubeTree.Leaf_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.ArrayCubeTree.Leaf_q(d) } 
  ArrayTypeMagic.ArrayCubeTree.Leaf_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.ArrayCubeTree.Leaf);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.ArrayCubeTree.Leaf_q(d) } 
  ArrayTypeMagic.ArrayCubeTree.Leaf_q(d)
     ==> (exists a#1#0#0: ref :: d == #ArrayTypeMagic.ArrayCubeTree.Leaf(a#1#0#0)));

function Tclass.ArrayTypeMagic.ArrayCubeTree(Ty) : Ty;

const unique Tagclass.ArrayTypeMagic.ArrayCubeTree: TyTag;

// Tclass.ArrayTypeMagic.ArrayCubeTree Tag
axiom (forall ArrayTypeMagic.ArrayCubeTree$T: Ty :: 
  { Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T) } 
  Tag(Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T))
       == Tagclass.ArrayTypeMagic.ArrayCubeTree
     && TagFamily(Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T))
       == tytagFamily$ArrayCubeTree);

// Tclass.ArrayTypeMagic.ArrayCubeTree injectivity 0
axiom (forall ArrayTypeMagic.ArrayCubeTree$T: Ty :: 
  { Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T) } 
  Tclass.ArrayTypeMagic.ArrayCubeTree_0(Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T))
     == ArrayTypeMagic.ArrayCubeTree$T);

function Tclass.ArrayTypeMagic.ArrayCubeTree_0(Ty) : Ty;

// Box/unbox axiom for Tclass.ArrayTypeMagic.ArrayCubeTree
axiom (forall ArrayTypeMagic.ArrayCubeTree$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T)) } 
  $IsBox(bx, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T)));

// Constructor $Is
axiom (forall ArrayTypeMagic.ArrayCubeTree$T: Ty, a#2#0#0: ref :: 
  { $Is(#ArrayTypeMagic.ArrayCubeTree.Leaf(a#2#0#0), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T)) } 
  $Is(#ArrayTypeMagic.ArrayCubeTree.Leaf(a#2#0#0), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T))
     <==> $Is(a#2#0#0, Tclass._System.array3(ArrayTypeMagic.ArrayCubeTree$T)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.ArrayCubeTree$T: Ty, a#3#0#0: ref, $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.ArrayCubeTree.Leaf(a#3#0#0), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.ArrayCubeTree.Leaf(a#3#0#0), 
        Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), 
        $h)
       <==> $IsAlloc(a#3#0#0, Tclass._System.array3(ArrayTypeMagic.ArrayCubeTree$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.ArrayCubeTree$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.ArrayCubeTree._h4(d), 
      Tclass._System.array3(ArrayTypeMagic.ArrayCubeTree$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.ArrayCubeTree.Leaf_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), $h)
     ==> $IsAlloc(ArrayTypeMagic.ArrayCubeTree._h4(d), 
      Tclass._System.array3(ArrayTypeMagic.ArrayCubeTree$T), 
      $h));

// Constructor literal
axiom (forall a#4#0#0: ref :: 
  { #ArrayTypeMagic.ArrayCubeTree.Leaf(Lit(a#4#0#0)) } 
  #ArrayTypeMagic.ArrayCubeTree.Leaf(Lit(a#4#0#0))
     == Lit(#ArrayTypeMagic.ArrayCubeTree.Leaf(a#4#0#0)));

function ArrayTypeMagic.ArrayCubeTree._h4(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#5#0#0: ref :: 
  { #ArrayTypeMagic.ArrayCubeTree.Leaf(a#5#0#0) } 
  ArrayTypeMagic.ArrayCubeTree._h4(#ArrayTypeMagic.ArrayCubeTree.Leaf(a#5#0#0))
     == a#5#0#0);

// Constructor function declaration
function #ArrayTypeMagic.ArrayCubeTree.Node(DatatypeType, DatatypeType) : DatatypeType;

const unique ##ArrayTypeMagic.ArrayCubeTree.Node: DtCtorId;

// Constructor identifier
axiom (forall a#6#0#0: DatatypeType, a#6#1#0: DatatypeType :: 
  { #ArrayTypeMagic.ArrayCubeTree.Node(a#6#0#0, a#6#1#0) } 
  DatatypeCtorId(#ArrayTypeMagic.ArrayCubeTree.Node(a#6#0#0, a#6#1#0))
     == ##ArrayTypeMagic.ArrayCubeTree.Node);

function ArrayTypeMagic.ArrayCubeTree.Node_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.ArrayCubeTree.Node_q(d) } 
  ArrayTypeMagic.ArrayCubeTree.Node_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.ArrayCubeTree.Node);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.ArrayCubeTree.Node_q(d) } 
  ArrayTypeMagic.ArrayCubeTree.Node_q(d)
     ==> (exists a#7#0#0: DatatypeType, a#7#1#0: DatatypeType :: 
      d == #ArrayTypeMagic.ArrayCubeTree.Node(a#7#0#0, a#7#1#0)));

// Constructor $Is
axiom (forall ArrayTypeMagic.ArrayCubeTree$T: Ty, a#8#0#0: DatatypeType, a#8#1#0: DatatypeType :: 
  { $Is(#ArrayTypeMagic.ArrayCubeTree.Node(a#8#0#0, a#8#1#0), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T)) } 
  $Is(#ArrayTypeMagic.ArrayCubeTree.Node(a#8#0#0, a#8#1#0), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T))
     <==> $Is(a#8#0#0, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T))
       && $Is(a#8#1#0, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.ArrayCubeTree$T: Ty, 
    a#9#0#0: DatatypeType, 
    a#9#1#0: DatatypeType, 
    $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.ArrayCubeTree.Node(a#9#0#0, a#9#1#0), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.ArrayCubeTree.Node(a#9#0#0, a#9#1#0), 
        Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), 
        $h)
       <==> $IsAlloc(a#9#0#0, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), $h)
         && $IsAlloc(a#9#1#0, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.ArrayCubeTree$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.ArrayCubeTree._h5(d), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.ArrayCubeTree.Node_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), $h)
     ==> $IsAlloc(ArrayTypeMagic.ArrayCubeTree._h5(d), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), 
      $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.ArrayCubeTree$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.ArrayCubeTree._h6(d), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.ArrayCubeTree.Node_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), $h)
     ==> $IsAlloc(ArrayTypeMagic.ArrayCubeTree._h6(d), 
      Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T), 
      $h));

// Constructor literal
axiom (forall a#10#0#0: DatatypeType, a#10#1#0: DatatypeType :: 
  { #ArrayTypeMagic.ArrayCubeTree.Node(Lit(a#10#0#0), Lit(a#10#1#0)) } 
  #ArrayTypeMagic.ArrayCubeTree.Node(Lit(a#10#0#0), Lit(a#10#1#0))
     == Lit(#ArrayTypeMagic.ArrayCubeTree.Node(a#10#0#0, a#10#1#0)));

function ArrayTypeMagic.ArrayCubeTree._h5(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#11#0#0: DatatypeType, a#11#1#0: DatatypeType :: 
  { #ArrayTypeMagic.ArrayCubeTree.Node(a#11#0#0, a#11#1#0) } 
  ArrayTypeMagic.ArrayCubeTree._h5(#ArrayTypeMagic.ArrayCubeTree.Node(a#11#0#0, a#11#1#0))
     == a#11#0#0);

// Inductive rank
axiom (forall a#12#0#0: DatatypeType, a#12#1#0: DatatypeType :: 
  { #ArrayTypeMagic.ArrayCubeTree.Node(a#12#0#0, a#12#1#0) } 
  DtRank(a#12#0#0)
     < DtRank(#ArrayTypeMagic.ArrayCubeTree.Node(a#12#0#0, a#12#1#0)));

function ArrayTypeMagic.ArrayCubeTree._h6(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#13#0#0: DatatypeType, a#13#1#0: DatatypeType :: 
  { #ArrayTypeMagic.ArrayCubeTree.Node(a#13#0#0, a#13#1#0) } 
  ArrayTypeMagic.ArrayCubeTree._h6(#ArrayTypeMagic.ArrayCubeTree.Node(a#13#0#0, a#13#1#0))
     == a#13#1#0);

// Inductive rank
axiom (forall a#14#0#0: DatatypeType, a#14#1#0: DatatypeType :: 
  { #ArrayTypeMagic.ArrayCubeTree.Node(a#14#0#0, a#14#1#0) } 
  DtRank(a#14#1#0)
     < DtRank(#ArrayTypeMagic.ArrayCubeTree.Node(a#14#0#0, a#14#1#0)));

// Depth-one case-split function
function $IsA#ArrayTypeMagic.ArrayCubeTree(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ArrayTypeMagic.ArrayCubeTree(d) } 
  $IsA#ArrayTypeMagic.ArrayCubeTree(d)
     ==> ArrayTypeMagic.ArrayCubeTree.Leaf_q(d) || ArrayTypeMagic.ArrayCubeTree.Node_q(d));

// Questionmark data type disjunctivity
axiom (forall ArrayTypeMagic.ArrayCubeTree$T: Ty, d: DatatypeType :: 
  { ArrayTypeMagic.ArrayCubeTree.Node_q(d), $Is(d, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T)) } 
    { ArrayTypeMagic.ArrayCubeTree.Leaf_q(d), $Is(d, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T)) } 
  $Is(d, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic.ArrayCubeTree$T))
     ==> ArrayTypeMagic.ArrayCubeTree.Leaf_q(d) || ArrayTypeMagic.ArrayCubeTree.Node_q(d));

// Datatype extensional equality declaration
function ArrayTypeMagic.ArrayCubeTree#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ArrayTypeMagic.ArrayCubeTree.Leaf
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.ArrayCubeTree#Equal(a, b), ArrayTypeMagic.ArrayCubeTree.Leaf_q(a) } 
    { ArrayTypeMagic.ArrayCubeTree#Equal(a, b), ArrayTypeMagic.ArrayCubeTree.Leaf_q(b) } 
  ArrayTypeMagic.ArrayCubeTree.Leaf_q(a) && ArrayTypeMagic.ArrayCubeTree.Leaf_q(b)
     ==> (ArrayTypeMagic.ArrayCubeTree#Equal(a, b)
       <==> ArrayTypeMagic.ArrayCubeTree._h4(a) == ArrayTypeMagic.ArrayCubeTree._h4(b)));

// Datatype extensional equality definition: #ArrayTypeMagic.ArrayCubeTree.Node
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.ArrayCubeTree#Equal(a, b), ArrayTypeMagic.ArrayCubeTree.Node_q(a) } 
    { ArrayTypeMagic.ArrayCubeTree#Equal(a, b), ArrayTypeMagic.ArrayCubeTree.Node_q(b) } 
  ArrayTypeMagic.ArrayCubeTree.Node_q(a) && ArrayTypeMagic.ArrayCubeTree.Node_q(b)
     ==> (ArrayTypeMagic.ArrayCubeTree#Equal(a, b)
       <==> ArrayTypeMagic.ArrayCubeTree#Equal(ArrayTypeMagic.ArrayCubeTree._h5(a), ArrayTypeMagic.ArrayCubeTree._h5(b))
         && ArrayTypeMagic.ArrayCubeTree#Equal(ArrayTypeMagic.ArrayCubeTree._h6(a), ArrayTypeMagic.ArrayCubeTree._h6(b))));

// Datatype extensionality axiom: ArrayTypeMagic.ArrayCubeTree
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.ArrayCubeTree#Equal(a, b) } 
  ArrayTypeMagic.ArrayCubeTree#Equal(a, b) <==> a == b);

const unique class.ArrayTypeMagic.ArrayCubeTree: ClassName;

// Constructor function declaration
function #ArrayTypeMagic.AnotherACT.Leaf(ref) : DatatypeType;

const unique ##ArrayTypeMagic.AnotherACT.Leaf: DtCtorId;

// Constructor identifier
axiom (forall a#15#0#0: ref :: 
  { #ArrayTypeMagic.AnotherACT.Leaf(a#15#0#0) } 
  DatatypeCtorId(#ArrayTypeMagic.AnotherACT.Leaf(a#15#0#0))
     == ##ArrayTypeMagic.AnotherACT.Leaf);

function ArrayTypeMagic.AnotherACT.Leaf_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.AnotherACT.Leaf_q(d) } 
  ArrayTypeMagic.AnotherACT.Leaf_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.AnotherACT.Leaf);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.AnotherACT.Leaf_q(d) } 
  ArrayTypeMagic.AnotherACT.Leaf_q(d)
     ==> (exists a#16#0#0: ref :: d == #ArrayTypeMagic.AnotherACT.Leaf(a#16#0#0)));

function Tclass.ArrayTypeMagic.AnotherACT(Ty) : Ty;

const unique Tagclass.ArrayTypeMagic.AnotherACT: TyTag;

// Tclass.ArrayTypeMagic.AnotherACT Tag
axiom (forall ArrayTypeMagic.AnotherACT$T: Ty :: 
  { Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T) } 
  Tag(Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T))
       == Tagclass.ArrayTypeMagic.AnotherACT
     && TagFamily(Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T))
       == tytagFamily$AnotherACT);

// Tclass.ArrayTypeMagic.AnotherACT injectivity 0
axiom (forall ArrayTypeMagic.AnotherACT$T: Ty :: 
  { Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T) } 
  Tclass.ArrayTypeMagic.AnotherACT_0(Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T))
     == ArrayTypeMagic.AnotherACT$T);

function Tclass.ArrayTypeMagic.AnotherACT_0(Ty) : Ty;

// Box/unbox axiom for Tclass.ArrayTypeMagic.AnotherACT
axiom (forall ArrayTypeMagic.AnotherACT$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T)) } 
  $IsBox(bx, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T)));

// Constructor $Is
axiom (forall ArrayTypeMagic.AnotherACT$T: Ty, a#17#0#0: ref :: 
  { $Is(#ArrayTypeMagic.AnotherACT.Leaf(a#17#0#0), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T)) } 
  $Is(#ArrayTypeMagic.AnotherACT.Leaf(a#17#0#0), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T))
     <==> $Is(a#17#0#0, Tclass._System.array3(ArrayTypeMagic.AnotherACT$T)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.AnotherACT$T: Ty, a#18#0#0: ref, $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.AnotherACT.Leaf(a#18#0#0), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.AnotherACT.Leaf(a#18#0#0), 
        Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), 
        $h)
       <==> $IsAlloc(a#18#0#0, Tclass._System.array3(ArrayTypeMagic.AnotherACT$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.AnotherACT$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.AnotherACT._h7(d), 
      Tclass._System.array3(ArrayTypeMagic.AnotherACT$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.AnotherACT.Leaf_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), $h)
     ==> $IsAlloc(ArrayTypeMagic.AnotherACT._h7(d), 
      Tclass._System.array3(ArrayTypeMagic.AnotherACT$T), 
      $h));

// Constructor literal
axiom (forall a#19#0#0: ref :: 
  { #ArrayTypeMagic.AnotherACT.Leaf(Lit(a#19#0#0)) } 
  #ArrayTypeMagic.AnotherACT.Leaf(Lit(a#19#0#0))
     == Lit(#ArrayTypeMagic.AnotherACT.Leaf(a#19#0#0)));

function ArrayTypeMagic.AnotherACT._h7(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#20#0#0: ref :: 
  { #ArrayTypeMagic.AnotherACT.Leaf(a#20#0#0) } 
  ArrayTypeMagic.AnotherACT._h7(#ArrayTypeMagic.AnotherACT.Leaf(a#20#0#0))
     == a#20#0#0);

// Constructor function declaration
function #ArrayTypeMagic.AnotherACT.Node(DatatypeType, DatatypeType) : DatatypeType;

const unique ##ArrayTypeMagic.AnotherACT.Node: DtCtorId;

// Constructor identifier
axiom (forall a#21#0#0: DatatypeType, a#21#1#0: DatatypeType :: 
  { #ArrayTypeMagic.AnotherACT.Node(a#21#0#0, a#21#1#0) } 
  DatatypeCtorId(#ArrayTypeMagic.AnotherACT.Node(a#21#0#0, a#21#1#0))
     == ##ArrayTypeMagic.AnotherACT.Node);

function ArrayTypeMagic.AnotherACT.Node_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.AnotherACT.Node_q(d) } 
  ArrayTypeMagic.AnotherACT.Node_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.AnotherACT.Node);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.AnotherACT.Node_q(d) } 
  ArrayTypeMagic.AnotherACT.Node_q(d)
     ==> (exists a#22#0#0: DatatypeType, a#22#1#0: DatatypeType :: 
      d == #ArrayTypeMagic.AnotherACT.Node(a#22#0#0, a#22#1#0)));

// Constructor $Is
axiom (forall ArrayTypeMagic.AnotherACT$T: Ty, a#23#0#0: DatatypeType, a#23#1#0: DatatypeType :: 
  { $Is(#ArrayTypeMagic.AnotherACT.Node(a#23#0#0, a#23#1#0), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T)) } 
  $Is(#ArrayTypeMagic.AnotherACT.Node(a#23#0#0, a#23#1#0), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T))
     <==> $Is(a#23#0#0, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T))
       && $Is(a#23#1#0, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.AnotherACT$T: Ty, 
    a#24#0#0: DatatypeType, 
    a#24#1#0: DatatypeType, 
    $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.AnotherACT.Node(a#24#0#0, a#24#1#0), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.AnotherACT.Node(a#24#0#0, a#24#1#0), 
        Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), 
        $h)
       <==> $IsAlloc(a#24#0#0, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), $h)
         && $IsAlloc(a#24#1#0, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.AnotherACT$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.AnotherACT._h8(d), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.AnotherACT.Node_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), $h)
     ==> $IsAlloc(ArrayTypeMagic.AnotherACT._h8(d), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), 
      $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.AnotherACT$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.AnotherACT._h9(d), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.AnotherACT.Node_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), $h)
     ==> $IsAlloc(ArrayTypeMagic.AnotherACT._h9(d), 
      Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T), 
      $h));

// Constructor literal
axiom (forall a#25#0#0: DatatypeType, a#25#1#0: DatatypeType :: 
  { #ArrayTypeMagic.AnotherACT.Node(Lit(a#25#0#0), Lit(a#25#1#0)) } 
  #ArrayTypeMagic.AnotherACT.Node(Lit(a#25#0#0), Lit(a#25#1#0))
     == Lit(#ArrayTypeMagic.AnotherACT.Node(a#25#0#0, a#25#1#0)));

function ArrayTypeMagic.AnotherACT._h8(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#26#0#0: DatatypeType, a#26#1#0: DatatypeType :: 
  { #ArrayTypeMagic.AnotherACT.Node(a#26#0#0, a#26#1#0) } 
  ArrayTypeMagic.AnotherACT._h8(#ArrayTypeMagic.AnotherACT.Node(a#26#0#0, a#26#1#0))
     == a#26#0#0);

// Inductive rank
axiom (forall a#27#0#0: DatatypeType, a#27#1#0: DatatypeType :: 
  { #ArrayTypeMagic.AnotherACT.Node(a#27#0#0, a#27#1#0) } 
  DtRank(a#27#0#0) < DtRank(#ArrayTypeMagic.AnotherACT.Node(a#27#0#0, a#27#1#0)));

function ArrayTypeMagic.AnotherACT._h9(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#28#0#0: DatatypeType, a#28#1#0: DatatypeType :: 
  { #ArrayTypeMagic.AnotherACT.Node(a#28#0#0, a#28#1#0) } 
  ArrayTypeMagic.AnotherACT._h9(#ArrayTypeMagic.AnotherACT.Node(a#28#0#0, a#28#1#0))
     == a#28#1#0);

// Inductive rank
axiom (forall a#29#0#0: DatatypeType, a#29#1#0: DatatypeType :: 
  { #ArrayTypeMagic.AnotherACT.Node(a#29#0#0, a#29#1#0) } 
  DtRank(a#29#1#0) < DtRank(#ArrayTypeMagic.AnotherACT.Node(a#29#0#0, a#29#1#0)));

// Depth-one case-split function
function $IsA#ArrayTypeMagic.AnotherACT(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ArrayTypeMagic.AnotherACT(d) } 
  $IsA#ArrayTypeMagic.AnotherACT(d)
     ==> ArrayTypeMagic.AnotherACT.Leaf_q(d) || ArrayTypeMagic.AnotherACT.Node_q(d));

// Questionmark data type disjunctivity
axiom (forall ArrayTypeMagic.AnotherACT$T: Ty, d: DatatypeType :: 
  { ArrayTypeMagic.AnotherACT.Node_q(d), $Is(d, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T)) } 
    { ArrayTypeMagic.AnotherACT.Leaf_q(d), $Is(d, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T)) } 
  $Is(d, Tclass.ArrayTypeMagic.AnotherACT(ArrayTypeMagic.AnotherACT$T))
     ==> ArrayTypeMagic.AnotherACT.Leaf_q(d) || ArrayTypeMagic.AnotherACT.Node_q(d));

// Datatype extensional equality declaration
function ArrayTypeMagic.AnotherACT#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ArrayTypeMagic.AnotherACT.Leaf
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.AnotherACT#Equal(a, b), ArrayTypeMagic.AnotherACT.Leaf_q(a) } 
    { ArrayTypeMagic.AnotherACT#Equal(a, b), ArrayTypeMagic.AnotherACT.Leaf_q(b) } 
  ArrayTypeMagic.AnotherACT.Leaf_q(a) && ArrayTypeMagic.AnotherACT.Leaf_q(b)
     ==> (ArrayTypeMagic.AnotherACT#Equal(a, b)
       <==> ArrayTypeMagic.AnotherACT._h7(a) == ArrayTypeMagic.AnotherACT._h7(b)));

// Datatype extensional equality definition: #ArrayTypeMagic.AnotherACT.Node
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.AnotherACT#Equal(a, b), ArrayTypeMagic.AnotherACT.Node_q(a) } 
    { ArrayTypeMagic.AnotherACT#Equal(a, b), ArrayTypeMagic.AnotherACT.Node_q(b) } 
  ArrayTypeMagic.AnotherACT.Node_q(a) && ArrayTypeMagic.AnotherACT.Node_q(b)
     ==> (ArrayTypeMagic.AnotherACT#Equal(a, b)
       <==> ArrayTypeMagic.AnotherACT#Equal(ArrayTypeMagic.AnotherACT._h8(a), ArrayTypeMagic.AnotherACT._h8(b))
         && ArrayTypeMagic.AnotherACT#Equal(ArrayTypeMagic.AnotherACT._h9(a), ArrayTypeMagic.AnotherACT._h9(b))));

// Datatype extensionality axiom: ArrayTypeMagic.AnotherACT
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.AnotherACT#Equal(a, b) } 
  ArrayTypeMagic.AnotherACT#Equal(a, b) <==> a == b);

const unique class.ArrayTypeMagic.AnotherACT: ClassName;

// Constructor function declaration
function #ArrayTypeMagic.OneMoreACT.Leaf(ref) : DatatypeType;

const unique ##ArrayTypeMagic.OneMoreACT.Leaf: DtCtorId;

// Constructor identifier
axiom (forall a#30#0#0: ref :: 
  { #ArrayTypeMagic.OneMoreACT.Leaf(a#30#0#0) } 
  DatatypeCtorId(#ArrayTypeMagic.OneMoreACT.Leaf(a#30#0#0))
     == ##ArrayTypeMagic.OneMoreACT.Leaf);

function ArrayTypeMagic.OneMoreACT.Leaf_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.OneMoreACT.Leaf_q(d) } 
  ArrayTypeMagic.OneMoreACT.Leaf_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.OneMoreACT.Leaf);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.OneMoreACT.Leaf_q(d) } 
  ArrayTypeMagic.OneMoreACT.Leaf_q(d)
     ==> (exists a#31#0#0: ref :: d == #ArrayTypeMagic.OneMoreACT.Leaf(a#31#0#0)));

function Tclass.ArrayTypeMagic.OneMoreACT(Ty, Ty) : Ty;

const unique Tagclass.ArrayTypeMagic.OneMoreACT: TyTag;

// Tclass.ArrayTypeMagic.OneMoreACT Tag
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, ArrayTypeMagic.OneMoreACT$U: Ty :: 
  { Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U) } 
  Tag(Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
       == Tagclass.ArrayTypeMagic.OneMoreACT
     && TagFamily(Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
       == tytagFamily$OneMoreACT);

// Tclass.ArrayTypeMagic.OneMoreACT injectivity 0
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, ArrayTypeMagic.OneMoreACT$U: Ty :: 
  { Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U) } 
  Tclass.ArrayTypeMagic.OneMoreACT_0(Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
     == ArrayTypeMagic.OneMoreACT$T);

function Tclass.ArrayTypeMagic.OneMoreACT_0(Ty) : Ty;

// Tclass.ArrayTypeMagic.OneMoreACT injectivity 1
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, ArrayTypeMagic.OneMoreACT$U: Ty :: 
  { Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U) } 
  Tclass.ArrayTypeMagic.OneMoreACT_1(Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
     == ArrayTypeMagic.OneMoreACT$U);

function Tclass.ArrayTypeMagic.OneMoreACT_1(Ty) : Ty;

// Box/unbox axiom for Tclass.ArrayTypeMagic.OneMoreACT
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, ArrayTypeMagic.OneMoreACT$U: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U)) } 
  $IsBox(bx, 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U)));

// Constructor $Is
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, ArrayTypeMagic.OneMoreACT$U: Ty, a#32#0#0: ref :: 
  { $Is(#ArrayTypeMagic.OneMoreACT.Leaf(a#32#0#0), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U)) } 
  $Is(#ArrayTypeMagic.OneMoreACT.Leaf(a#32#0#0), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
     <==> $Is(a#32#0#0, Tclass._System.array3(ArrayTypeMagic.OneMoreACT$T)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, 
    ArrayTypeMagic.OneMoreACT$U: Ty, 
    a#33#0#0: ref, 
    $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.OneMoreACT.Leaf(a#33#0#0), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.OneMoreACT.Leaf(a#33#0#0), 
        Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
        $h)
       <==> $IsAlloc(a#33#0#0, Tclass._System.array3(ArrayTypeMagic.OneMoreACT$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.OneMoreACT$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.OneMoreACT._h10(d), 
      Tclass._System.array3(ArrayTypeMagic.OneMoreACT$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.OneMoreACT.Leaf_q(d)
       && (exists ArrayTypeMagic.OneMoreACT$U: Ty :: 
        { $IsAlloc(d, 
            Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
            $h) } 
        $IsAlloc(d, 
          Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
          $h))
     ==> $IsAlloc(ArrayTypeMagic.OneMoreACT._h10(d), 
      Tclass._System.array3(ArrayTypeMagic.OneMoreACT$T), 
      $h));

// Constructor literal
axiom (forall a#34#0#0: ref :: 
  { #ArrayTypeMagic.OneMoreACT.Leaf(Lit(a#34#0#0)) } 
  #ArrayTypeMagic.OneMoreACT.Leaf(Lit(a#34#0#0))
     == Lit(#ArrayTypeMagic.OneMoreACT.Leaf(a#34#0#0)));

function ArrayTypeMagic.OneMoreACT._h10(DatatypeType) : ref;

// Constructor injectivity
axiom (forall a#35#0#0: ref :: 
  { #ArrayTypeMagic.OneMoreACT.Leaf(a#35#0#0) } 
  ArrayTypeMagic.OneMoreACT._h10(#ArrayTypeMagic.OneMoreACT.Leaf(a#35#0#0))
     == a#35#0#0);

// Constructor function declaration
function #ArrayTypeMagic.OneMoreACT.Node(DatatypeType, DatatypeType) : DatatypeType;

const unique ##ArrayTypeMagic.OneMoreACT.Node: DtCtorId;

// Constructor identifier
axiom (forall a#36#0#0: DatatypeType, a#36#1#0: DatatypeType :: 
  { #ArrayTypeMagic.OneMoreACT.Node(a#36#0#0, a#36#1#0) } 
  DatatypeCtorId(#ArrayTypeMagic.OneMoreACT.Node(a#36#0#0, a#36#1#0))
     == ##ArrayTypeMagic.OneMoreACT.Node);

function ArrayTypeMagic.OneMoreACT.Node_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.OneMoreACT.Node_q(d) } 
  ArrayTypeMagic.OneMoreACT.Node_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.OneMoreACT.Node);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.OneMoreACT.Node_q(d) } 
  ArrayTypeMagic.OneMoreACT.Node_q(d)
     ==> (exists a#37#0#0: DatatypeType, a#37#1#0: DatatypeType :: 
      d == #ArrayTypeMagic.OneMoreACT.Node(a#37#0#0, a#37#1#0)));

// Constructor $Is
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, 
    ArrayTypeMagic.OneMoreACT$U: Ty, 
    a#38#0#0: DatatypeType, 
    a#38#1#0: DatatypeType :: 
  { $Is(#ArrayTypeMagic.OneMoreACT.Node(a#38#0#0, a#38#1#0), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U)) } 
  $Is(#ArrayTypeMagic.OneMoreACT.Node(a#38#0#0, a#38#1#0), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
     <==> $Is(a#38#0#0, 
        Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
       && $Is(a#38#1#0, 
        Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, 
    ArrayTypeMagic.OneMoreACT$U: Ty, 
    a#39#0#0: DatatypeType, 
    a#39#1#0: DatatypeType, 
    $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.OneMoreACT.Node(a#39#0#0, a#39#1#0), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.OneMoreACT.Node(a#39#0#0, a#39#1#0), 
        Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
        $h)
       <==> $IsAlloc(a#39#0#0, 
          Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
          $h)
         && $IsAlloc(a#39#1#0, 
          Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
          $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, 
    ArrayTypeMagic.OneMoreACT$T: Ty, 
    ArrayTypeMagic.OneMoreACT$U: Ty, 
    $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.OneMoreACT._h11(d), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.OneMoreACT.Node_q(d)
       && $IsAlloc(d, 
        Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
        $h)
     ==> $IsAlloc(ArrayTypeMagic.OneMoreACT._h11(d), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
      $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, 
    ArrayTypeMagic.OneMoreACT$T: Ty, 
    ArrayTypeMagic.OneMoreACT$U: Ty, 
    $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.OneMoreACT._h12(d), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.OneMoreACT.Node_q(d)
       && $IsAlloc(d, 
        Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
        $h)
     ==> $IsAlloc(ArrayTypeMagic.OneMoreACT._h12(d), 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U), 
      $h));

// Constructor literal
axiom (forall a#40#0#0: DatatypeType, a#40#1#0: DatatypeType :: 
  { #ArrayTypeMagic.OneMoreACT.Node(Lit(a#40#0#0), Lit(a#40#1#0)) } 
  #ArrayTypeMagic.OneMoreACT.Node(Lit(a#40#0#0), Lit(a#40#1#0))
     == Lit(#ArrayTypeMagic.OneMoreACT.Node(a#40#0#0, a#40#1#0)));

function ArrayTypeMagic.OneMoreACT._h11(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#41#0#0: DatatypeType, a#41#1#0: DatatypeType :: 
  { #ArrayTypeMagic.OneMoreACT.Node(a#41#0#0, a#41#1#0) } 
  ArrayTypeMagic.OneMoreACT._h11(#ArrayTypeMagic.OneMoreACT.Node(a#41#0#0, a#41#1#0))
     == a#41#0#0);

// Inductive rank
axiom (forall a#42#0#0: DatatypeType, a#42#1#0: DatatypeType :: 
  { #ArrayTypeMagic.OneMoreACT.Node(a#42#0#0, a#42#1#0) } 
  DtRank(a#42#0#0) < DtRank(#ArrayTypeMagic.OneMoreACT.Node(a#42#0#0, a#42#1#0)));

function ArrayTypeMagic.OneMoreACT._h12(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#43#0#0: DatatypeType, a#43#1#0: DatatypeType :: 
  { #ArrayTypeMagic.OneMoreACT.Node(a#43#0#0, a#43#1#0) } 
  ArrayTypeMagic.OneMoreACT._h12(#ArrayTypeMagic.OneMoreACT.Node(a#43#0#0, a#43#1#0))
     == a#43#1#0);

// Inductive rank
axiom (forall a#44#0#0: DatatypeType, a#44#1#0: DatatypeType :: 
  { #ArrayTypeMagic.OneMoreACT.Node(a#44#0#0, a#44#1#0) } 
  DtRank(a#44#1#0) < DtRank(#ArrayTypeMagic.OneMoreACT.Node(a#44#0#0, a#44#1#0)));

// Depth-one case-split function
function $IsA#ArrayTypeMagic.OneMoreACT(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ArrayTypeMagic.OneMoreACT(d) } 
  $IsA#ArrayTypeMagic.OneMoreACT(d)
     ==> ArrayTypeMagic.OneMoreACT.Leaf_q(d) || ArrayTypeMagic.OneMoreACT.Node_q(d));

// Questionmark data type disjunctivity
axiom (forall ArrayTypeMagic.OneMoreACT$T: Ty, 
    ArrayTypeMagic.OneMoreACT$U: Ty, 
    d: DatatypeType :: 
  { ArrayTypeMagic.OneMoreACT.Node_q(d), $Is(d, 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U)) } 
    { ArrayTypeMagic.OneMoreACT.Leaf_q(d), $Is(d, 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U)) } 
  $Is(d, 
      Tclass.ArrayTypeMagic.OneMoreACT(ArrayTypeMagic.OneMoreACT$T, ArrayTypeMagic.OneMoreACT$U))
     ==> ArrayTypeMagic.OneMoreACT.Leaf_q(d) || ArrayTypeMagic.OneMoreACT.Node_q(d));

// Datatype extensional equality declaration
function ArrayTypeMagic.OneMoreACT#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ArrayTypeMagic.OneMoreACT.Leaf
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.OneMoreACT#Equal(a, b), ArrayTypeMagic.OneMoreACT.Leaf_q(a) } 
    { ArrayTypeMagic.OneMoreACT#Equal(a, b), ArrayTypeMagic.OneMoreACT.Leaf_q(b) } 
  ArrayTypeMagic.OneMoreACT.Leaf_q(a) && ArrayTypeMagic.OneMoreACT.Leaf_q(b)
     ==> (ArrayTypeMagic.OneMoreACT#Equal(a, b)
       <==> ArrayTypeMagic.OneMoreACT._h10(a) == ArrayTypeMagic.OneMoreACT._h10(b)));

// Datatype extensional equality definition: #ArrayTypeMagic.OneMoreACT.Node
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.OneMoreACT#Equal(a, b), ArrayTypeMagic.OneMoreACT.Node_q(a) } 
    { ArrayTypeMagic.OneMoreACT#Equal(a, b), ArrayTypeMagic.OneMoreACT.Node_q(b) } 
  ArrayTypeMagic.OneMoreACT.Node_q(a) && ArrayTypeMagic.OneMoreACT.Node_q(b)
     ==> (ArrayTypeMagic.OneMoreACT#Equal(a, b)
       <==> ArrayTypeMagic.OneMoreACT#Equal(ArrayTypeMagic.OneMoreACT._h11(a), ArrayTypeMagic.OneMoreACT._h11(b))
         && ArrayTypeMagic.OneMoreACT#Equal(ArrayTypeMagic.OneMoreACT._h12(a), ArrayTypeMagic.OneMoreACT._h12(b))));

// Datatype extensionality axiom: ArrayTypeMagic.OneMoreACT
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.OneMoreACT#Equal(a, b) } 
  ArrayTypeMagic.OneMoreACT#Equal(a, b) <==> a == b);

const unique class.ArrayTypeMagic.OneMoreACT: ClassName;

// Constructor function declaration
function #ArrayTypeMagic.Nat.Zero() : DatatypeType;

const unique ##ArrayTypeMagic.Nat.Zero: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#ArrayTypeMagic.Nat.Zero()) == ##ArrayTypeMagic.Nat.Zero;

function ArrayTypeMagic.Nat.Zero_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.Nat.Zero_q(d) } 
  ArrayTypeMagic.Nat.Zero_q(d) <==> DatatypeCtorId(d) == ##ArrayTypeMagic.Nat.Zero);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.Nat.Zero_q(d) } 
  ArrayTypeMagic.Nat.Zero_q(d) ==> d == #ArrayTypeMagic.Nat.Zero());

function Tclass.ArrayTypeMagic.Nat() : Ty;

const unique Tagclass.ArrayTypeMagic.Nat: TyTag;

// Tclass.ArrayTypeMagic.Nat Tag
axiom Tag(Tclass.ArrayTypeMagic.Nat()) == Tagclass.ArrayTypeMagic.Nat
   && TagFamily(Tclass.ArrayTypeMagic.Nat()) == tytagFamily$Nat;

// Box/unbox axiom for Tclass.ArrayTypeMagic.Nat
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ArrayTypeMagic.Nat()) } 
  $IsBox(bx, Tclass.ArrayTypeMagic.Nat())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.ArrayTypeMagic.Nat()));

// Constructor $Is
axiom $Is(#ArrayTypeMagic.Nat.Zero(), Tclass.ArrayTypeMagic.Nat());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.Nat.Zero(), Tclass.ArrayTypeMagic.Nat(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#ArrayTypeMagic.Nat.Zero(), Tclass.ArrayTypeMagic.Nat(), $h));

// Constructor literal
axiom #ArrayTypeMagic.Nat.Zero() == Lit(#ArrayTypeMagic.Nat.Zero());

// Constructor function declaration
function #ArrayTypeMagic.Nat.Succ(DatatypeType) : DatatypeType;

const unique ##ArrayTypeMagic.Nat.Succ: DtCtorId;

// Constructor identifier
axiom (forall a#50#0#0: DatatypeType :: 
  { #ArrayTypeMagic.Nat.Succ(a#50#0#0) } 
  DatatypeCtorId(#ArrayTypeMagic.Nat.Succ(a#50#0#0)) == ##ArrayTypeMagic.Nat.Succ);

function ArrayTypeMagic.Nat.Succ_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.Nat.Succ_q(d) } 
  ArrayTypeMagic.Nat.Succ_q(d) <==> DatatypeCtorId(d) == ##ArrayTypeMagic.Nat.Succ);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.Nat.Succ_q(d) } 
  ArrayTypeMagic.Nat.Succ_q(d)
     ==> (exists a#51#0#0: DatatypeType :: d == #ArrayTypeMagic.Nat.Succ(a#51#0#0)));

// Constructor $Is
axiom (forall a#52#0#0: DatatypeType :: 
  { $Is(#ArrayTypeMagic.Nat.Succ(a#52#0#0), Tclass.ArrayTypeMagic.Nat()) } 
  $Is(#ArrayTypeMagic.Nat.Succ(a#52#0#0), Tclass.ArrayTypeMagic.Nat())
     <==> $Is(a#52#0#0, Tclass.ArrayTypeMagic.Nat()));

// Constructor $IsAlloc
axiom (forall a#53#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.Nat.Succ(a#53#0#0), Tclass.ArrayTypeMagic.Nat(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.Nat.Succ(a#53#0#0), Tclass.ArrayTypeMagic.Nat(), $h)
       <==> $IsAlloc(a#53#0#0, Tclass.ArrayTypeMagic.Nat(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.Nat._h14(d), Tclass.ArrayTypeMagic.Nat(), $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.Nat.Succ_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.Nat(), $h)
     ==> $IsAlloc(ArrayTypeMagic.Nat._h14(d), Tclass.ArrayTypeMagic.Nat(), $h));

// Constructor literal
axiom (forall a#54#0#0: DatatypeType :: 
  { #ArrayTypeMagic.Nat.Succ(Lit(a#54#0#0)) } 
  #ArrayTypeMagic.Nat.Succ(Lit(a#54#0#0))
     == Lit(#ArrayTypeMagic.Nat.Succ(a#54#0#0)));

function ArrayTypeMagic.Nat._h14(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#55#0#0: DatatypeType :: 
  { #ArrayTypeMagic.Nat.Succ(a#55#0#0) } 
  ArrayTypeMagic.Nat._h14(#ArrayTypeMagic.Nat.Succ(a#55#0#0)) == a#55#0#0);

// Inductive rank
axiom (forall a#56#0#0: DatatypeType :: 
  { #ArrayTypeMagic.Nat.Succ(a#56#0#0) } 
  DtRank(a#56#0#0) < DtRank(#ArrayTypeMagic.Nat.Succ(a#56#0#0)));

// Depth-one case-split function
function $IsA#ArrayTypeMagic.Nat(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ArrayTypeMagic.Nat(d) } 
  $IsA#ArrayTypeMagic.Nat(d)
     ==> ArrayTypeMagic.Nat.Zero_q(d) || ArrayTypeMagic.Nat.Succ_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.Nat.Succ_q(d), $Is(d, Tclass.ArrayTypeMagic.Nat()) } 
    { ArrayTypeMagic.Nat.Zero_q(d), $Is(d, Tclass.ArrayTypeMagic.Nat()) } 
  $Is(d, Tclass.ArrayTypeMagic.Nat())
     ==> ArrayTypeMagic.Nat.Zero_q(d) || ArrayTypeMagic.Nat.Succ_q(d));

// Datatype extensional equality declaration
function ArrayTypeMagic.Nat#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ArrayTypeMagic.Nat.Zero
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.Nat#Equal(a, b), ArrayTypeMagic.Nat.Zero_q(a) } 
    { ArrayTypeMagic.Nat#Equal(a, b), ArrayTypeMagic.Nat.Zero_q(b) } 
  ArrayTypeMagic.Nat.Zero_q(a) && ArrayTypeMagic.Nat.Zero_q(b)
     ==> (ArrayTypeMagic.Nat#Equal(a, b) <==> true));

// Datatype extensional equality definition: #ArrayTypeMagic.Nat.Succ
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.Nat#Equal(a, b), ArrayTypeMagic.Nat.Succ_q(a) } 
    { ArrayTypeMagic.Nat#Equal(a, b), ArrayTypeMagic.Nat.Succ_q(b) } 
  ArrayTypeMagic.Nat.Succ_q(a) && ArrayTypeMagic.Nat.Succ_q(b)
     ==> (ArrayTypeMagic.Nat#Equal(a, b)
       <==> ArrayTypeMagic.Nat#Equal(ArrayTypeMagic.Nat._h14(a), ArrayTypeMagic.Nat._h14(b))));

// Datatype extensionality axiom: ArrayTypeMagic.Nat
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.Nat#Equal(a, b) } 
  ArrayTypeMagic.Nat#Equal(a, b) <==> a == b);

const unique class.ArrayTypeMagic.Nat: ClassName;

// Constructor function declaration
function #ArrayTypeMagic.List.Nil() : DatatypeType;

const unique ##ArrayTypeMagic.List.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#ArrayTypeMagic.List.Nil()) == ##ArrayTypeMagic.List.Nil;

function ArrayTypeMagic.List.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.List.Nil_q(d) } 
  ArrayTypeMagic.List.Nil_q(d) <==> DatatypeCtorId(d) == ##ArrayTypeMagic.List.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.List.Nil_q(d) } 
  ArrayTypeMagic.List.Nil_q(d) ==> d == #ArrayTypeMagic.List.Nil());

function Tclass.ArrayTypeMagic.List(Ty) : Ty;

const unique Tagclass.ArrayTypeMagic.List: TyTag;

// Tclass.ArrayTypeMagic.List Tag
axiom (forall ArrayTypeMagic.List$T: Ty :: 
  { Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T) } 
  Tag(Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T))
       == Tagclass.ArrayTypeMagic.List
     && TagFamily(Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)) == tytagFamily$List);

// Tclass.ArrayTypeMagic.List injectivity 0
axiom (forall ArrayTypeMagic.List$T: Ty :: 
  { Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T) } 
  Tclass.ArrayTypeMagic.List_0(Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T))
     == ArrayTypeMagic.List$T);

function Tclass.ArrayTypeMagic.List_0(Ty) : Ty;

// Box/unbox axiom for Tclass.ArrayTypeMagic.List
axiom (forall ArrayTypeMagic.List$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)) } 
  $IsBox(bx, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)));

// Constructor $Is
axiom (forall ArrayTypeMagic.List$T: Ty :: 
  { $Is(#ArrayTypeMagic.List.Nil(), Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)) } 
  $Is(#ArrayTypeMagic.List.Nil(), Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.List$T: Ty, $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.List.Nil(), 
      Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#ArrayTypeMagic.List.Nil(), 
      Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), 
      $h));

// Constructor literal
axiom #ArrayTypeMagic.List.Nil() == Lit(#ArrayTypeMagic.List.Nil());

// Constructor function declaration
function #ArrayTypeMagic.List.Cons(Box, DatatypeType) : DatatypeType;

const unique ##ArrayTypeMagic.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#62#0#0: Box, a#62#1#0: DatatypeType :: 
  { #ArrayTypeMagic.List.Cons(a#62#0#0, a#62#1#0) } 
  DatatypeCtorId(#ArrayTypeMagic.List.Cons(a#62#0#0, a#62#1#0))
     == ##ArrayTypeMagic.List.Cons);

function ArrayTypeMagic.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.List.Cons_q(d) } 
  ArrayTypeMagic.List.Cons_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.List.Cons_q(d) } 
  ArrayTypeMagic.List.Cons_q(d)
     ==> (exists a#63#0#0: Box, a#63#1#0: DatatypeType :: 
      d == #ArrayTypeMagic.List.Cons(a#63#0#0, a#63#1#0)));

// Constructor $Is
axiom (forall ArrayTypeMagic.List$T: Ty, a#64#0#0: Box, a#64#1#0: DatatypeType :: 
  { $Is(#ArrayTypeMagic.List.Cons(a#64#0#0, a#64#1#0), 
      Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)) } 
  $Is(#ArrayTypeMagic.List.Cons(a#64#0#0, a#64#1#0), 
      Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T))
     <==> $IsBox(a#64#0#0, ArrayTypeMagic.List$T)
       && $Is(a#64#1#0, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.List$T: Ty, a#65#0#0: Box, a#65#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.List.Cons(a#65#0#0, a#65#1#0), 
      Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.List.Cons(a#65#0#0, a#65#1#0), 
        Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), 
        $h)
       <==> $IsAllocBox(a#65#0#0, ArrayTypeMagic.List$T, $h)
         && $IsAlloc(a#65#1#0, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.List$T: Ty, $h: Heap :: 
  { $IsAllocBox(ArrayTypeMagic.List._h15(d), ArrayTypeMagic.List$T, $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.List.Cons_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), $h)
     ==> $IsAllocBox(ArrayTypeMagic.List._h15(d), ArrayTypeMagic.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.List$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.List._h16(d), 
      Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.List.Cons_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), $h)
     ==> $IsAlloc(ArrayTypeMagic.List._h16(d), 
      Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T), 
      $h));

// Constructor literal
axiom (forall a#66#0#0: Box, a#66#1#0: DatatypeType :: 
  { #ArrayTypeMagic.List.Cons(Lit(a#66#0#0), Lit(a#66#1#0)) } 
  #ArrayTypeMagic.List.Cons(Lit(a#66#0#0), Lit(a#66#1#0))
     == Lit(#ArrayTypeMagic.List.Cons(a#66#0#0, a#66#1#0)));

function ArrayTypeMagic.List._h15(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#67#0#0: Box, a#67#1#0: DatatypeType :: 
  { #ArrayTypeMagic.List.Cons(a#67#0#0, a#67#1#0) } 
  ArrayTypeMagic.List._h15(#ArrayTypeMagic.List.Cons(a#67#0#0, a#67#1#0))
     == a#67#0#0);

// Inductive rank
axiom (forall a#68#0#0: Box, a#68#1#0: DatatypeType :: 
  { #ArrayTypeMagic.List.Cons(a#68#0#0, a#68#1#0) } 
  BoxRank(a#68#0#0) < DtRank(#ArrayTypeMagic.List.Cons(a#68#0#0, a#68#1#0)));

function ArrayTypeMagic.List._h16(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#69#0#0: Box, a#69#1#0: DatatypeType :: 
  { #ArrayTypeMagic.List.Cons(a#69#0#0, a#69#1#0) } 
  ArrayTypeMagic.List._h16(#ArrayTypeMagic.List.Cons(a#69#0#0, a#69#1#0))
     == a#69#1#0);

// Inductive rank
axiom (forall a#70#0#0: Box, a#70#1#0: DatatypeType :: 
  { #ArrayTypeMagic.List.Cons(a#70#0#0, a#70#1#0) } 
  DtRank(a#70#1#0) < DtRank(#ArrayTypeMagic.List.Cons(a#70#0#0, a#70#1#0)));

// Depth-one case-split function
function $IsA#ArrayTypeMagic.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ArrayTypeMagic.List(d) } 
  $IsA#ArrayTypeMagic.List(d)
     ==> ArrayTypeMagic.List.Nil_q(d) || ArrayTypeMagic.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall ArrayTypeMagic.List$T: Ty, d: DatatypeType :: 
  { ArrayTypeMagic.List.Cons_q(d), $Is(d, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)) } 
    { ArrayTypeMagic.List.Nil_q(d), $Is(d, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T)) } 
  $Is(d, Tclass.ArrayTypeMagic.List(ArrayTypeMagic.List$T))
     ==> ArrayTypeMagic.List.Nil_q(d) || ArrayTypeMagic.List.Cons_q(d));

// Datatype extensional equality declaration
function ArrayTypeMagic.List#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ArrayTypeMagic.List.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.List#Equal(a, b), ArrayTypeMagic.List.Nil_q(a) } 
    { ArrayTypeMagic.List#Equal(a, b), ArrayTypeMagic.List.Nil_q(b) } 
  ArrayTypeMagic.List.Nil_q(a) && ArrayTypeMagic.List.Nil_q(b)
     ==> (ArrayTypeMagic.List#Equal(a, b) <==> true));

// Datatype extensional equality definition: #ArrayTypeMagic.List.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.List#Equal(a, b), ArrayTypeMagic.List.Cons_q(a) } 
    { ArrayTypeMagic.List#Equal(a, b), ArrayTypeMagic.List.Cons_q(b) } 
  ArrayTypeMagic.List.Cons_q(a) && ArrayTypeMagic.List.Cons_q(b)
     ==> (ArrayTypeMagic.List#Equal(a, b)
       <==> ArrayTypeMagic.List._h15(a) == ArrayTypeMagic.List._h15(b)
         && ArrayTypeMagic.List#Equal(ArrayTypeMagic.List._h16(a), ArrayTypeMagic.List._h16(b))));

// Datatype extensionality axiom: ArrayTypeMagic.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.List#Equal(a, b) } 
  ArrayTypeMagic.List#Equal(a, b) <==> a == b);

const unique class.ArrayTypeMagic.List: ClassName;

// Constructor function declaration
function #ArrayTypeMagic.Cell.Mk(Box) : DatatypeType;

const unique ##ArrayTypeMagic.Cell.Mk: DtCtorId;

// Constructor identifier
axiom (forall a#71#0#0: Box :: 
  { #ArrayTypeMagic.Cell.Mk(a#71#0#0) } 
  DatatypeCtorId(#ArrayTypeMagic.Cell.Mk(a#71#0#0)) == ##ArrayTypeMagic.Cell.Mk);

function ArrayTypeMagic.Cell.Mk_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.Cell.Mk_q(d) } 
  ArrayTypeMagic.Cell.Mk_q(d) <==> DatatypeCtorId(d) == ##ArrayTypeMagic.Cell.Mk);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.Cell.Mk_q(d) } 
  ArrayTypeMagic.Cell.Mk_q(d)
     ==> (exists a#72#0#0: Box :: d == #ArrayTypeMagic.Cell.Mk(a#72#0#0)));

function Tclass.ArrayTypeMagic.Cell(Ty) : Ty;

const unique Tagclass.ArrayTypeMagic.Cell: TyTag;

// Tclass.ArrayTypeMagic.Cell Tag
axiom (forall ArrayTypeMagic.Cell$T: Ty :: 
  { Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T) } 
  Tag(Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T))
       == Tagclass.ArrayTypeMagic.Cell
     && TagFamily(Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T)) == tytagFamily$Cell);

// Tclass.ArrayTypeMagic.Cell injectivity 0
axiom (forall ArrayTypeMagic.Cell$T: Ty :: 
  { Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T) } 
  Tclass.ArrayTypeMagic.Cell_0(Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T))
     == ArrayTypeMagic.Cell$T);

function Tclass.ArrayTypeMagic.Cell_0(Ty) : Ty;

// Box/unbox axiom for Tclass.ArrayTypeMagic.Cell
axiom (forall ArrayTypeMagic.Cell$T: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T)) } 
  $IsBox(bx, Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T)));

// Constructor $Is
axiom (forall ArrayTypeMagic.Cell$T: Ty, a#73#0#0: Box :: 
  { $Is(#ArrayTypeMagic.Cell.Mk(a#73#0#0), 
      Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T)) } 
  $Is(#ArrayTypeMagic.Cell.Mk(a#73#0#0), 
      Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T))
     <==> $IsBox(a#73#0#0, ArrayTypeMagic.Cell$T));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.Cell$T: Ty, a#74#0#0: Box, $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.Cell.Mk(a#74#0#0), 
      Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.Cell.Mk(a#74#0#0), 
        Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T), 
        $h)
       <==> $IsAllocBox(a#74#0#0, ArrayTypeMagic.Cell$T, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.Cell$T: Ty, $h: Heap :: 
  { $IsAllocBox(ArrayTypeMagic.Cell._h17(d), ArrayTypeMagic.Cell$T, $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.Cell.Mk_q(d)
       && $IsAlloc(d, Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T), $h)
     ==> $IsAllocBox(ArrayTypeMagic.Cell._h17(d), ArrayTypeMagic.Cell$T, $h));

// Constructor literal
axiom (forall a#75#0#0: Box :: 
  { #ArrayTypeMagic.Cell.Mk(Lit(a#75#0#0)) } 
  #ArrayTypeMagic.Cell.Mk(Lit(a#75#0#0)) == Lit(#ArrayTypeMagic.Cell.Mk(a#75#0#0)));

function ArrayTypeMagic.Cell._h17(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#76#0#0: Box :: 
  { #ArrayTypeMagic.Cell.Mk(a#76#0#0) } 
  ArrayTypeMagic.Cell._h17(#ArrayTypeMagic.Cell.Mk(a#76#0#0)) == a#76#0#0);

// Inductive rank
axiom (forall a#77#0#0: Box :: 
  { #ArrayTypeMagic.Cell.Mk(a#77#0#0) } 
  BoxRank(a#77#0#0) < DtRank(#ArrayTypeMagic.Cell.Mk(a#77#0#0)));

// Depth-one case-split function
function $IsA#ArrayTypeMagic.Cell(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ArrayTypeMagic.Cell(d) } 
  $IsA#ArrayTypeMagic.Cell(d) ==> ArrayTypeMagic.Cell.Mk_q(d));

// Questionmark data type disjunctivity
axiom (forall ArrayTypeMagic.Cell$T: Ty, d: DatatypeType :: 
  { ArrayTypeMagic.Cell.Mk_q(d), $Is(d, Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T)) } 
  $Is(d, Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.Cell$T))
     ==> ArrayTypeMagic.Cell.Mk_q(d));

// Datatype extensional equality declaration
function ArrayTypeMagic.Cell#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ArrayTypeMagic.Cell.Mk
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.Cell#Equal(a, b) } 
  true
     ==> (ArrayTypeMagic.Cell#Equal(a, b)
       <==> ArrayTypeMagic.Cell._h17(a) == ArrayTypeMagic.Cell._h17(b)));

// Datatype extensionality axiom: ArrayTypeMagic.Cell
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.Cell#Equal(a, b) } 
  ArrayTypeMagic.Cell#Equal(a, b) <==> a == b);

const unique class.ArrayTypeMagic.Cell: ClassName;

// Constructor function declaration
function #ArrayTypeMagic.DList.Nil(DatatypeType) : DatatypeType;

const unique ##ArrayTypeMagic.DList.Nil: DtCtorId;

// Constructor identifier
axiom (forall a#78#0#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Nil(a#78#0#0) } 
  DatatypeCtorId(#ArrayTypeMagic.DList.Nil(a#78#0#0))
     == ##ArrayTypeMagic.DList.Nil);

function ArrayTypeMagic.DList.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.DList.Nil_q(d) } 
  ArrayTypeMagic.DList.Nil_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.DList.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.DList.Nil_q(d) } 
  ArrayTypeMagic.DList.Nil_q(d)
     ==> (exists a#79#0#0: DatatypeType :: d == #ArrayTypeMagic.DList.Nil(a#79#0#0)));

function Tclass.ArrayTypeMagic.DList(Ty, Ty) : Ty;

const unique Tagclass.ArrayTypeMagic.DList: TyTag;

// Tclass.ArrayTypeMagic.DList Tag
axiom (forall ArrayTypeMagic.DList$T: Ty, ArrayTypeMagic.DList$U: Ty :: 
  { Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U) } 
  Tag(Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U))
       == Tagclass.ArrayTypeMagic.DList
     && TagFamily(Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U))
       == tytagFamily$DList);

// Tclass.ArrayTypeMagic.DList injectivity 0
axiom (forall ArrayTypeMagic.DList$T: Ty, ArrayTypeMagic.DList$U: Ty :: 
  { Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U) } 
  Tclass.ArrayTypeMagic.DList_0(Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U))
     == ArrayTypeMagic.DList$T);

function Tclass.ArrayTypeMagic.DList_0(Ty) : Ty;

// Tclass.ArrayTypeMagic.DList injectivity 1
axiom (forall ArrayTypeMagic.DList$T: Ty, ArrayTypeMagic.DList$U: Ty :: 
  { Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U) } 
  Tclass.ArrayTypeMagic.DList_1(Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U))
     == ArrayTypeMagic.DList$U);

function Tclass.ArrayTypeMagic.DList_1(Ty) : Ty;

// Box/unbox axiom for Tclass.ArrayTypeMagic.DList
axiom (forall ArrayTypeMagic.DList$T: Ty, ArrayTypeMagic.DList$U: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U)) } 
  $IsBox(bx, Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, 
        Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U)));

// Constructor $Is
axiom (forall ArrayTypeMagic.DList$T: Ty, ArrayTypeMagic.DList$U: Ty, a#80#0#0: DatatypeType :: 
  { $Is(#ArrayTypeMagic.DList.Nil(a#80#0#0), 
      Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U)) } 
  $Is(#ArrayTypeMagic.DList.Nil(a#80#0#0), 
      Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U))
     <==> $Is(a#80#0#0, Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.DList$T)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.DList$T: Ty, 
    ArrayTypeMagic.DList$U: Ty, 
    a#81#0#0: DatatypeType, 
    $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.DList.Nil(a#81#0#0), 
      Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.DList.Nil(a#81#0#0), 
        Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
        $h)
       <==> $IsAlloc(a#81#0#0, Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.DList$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.DList$T: Ty, $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.DList._h18(d), 
      Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.DList$T), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.DList.Nil_q(d)
       && (exists ArrayTypeMagic.DList$U: Ty :: 
        { $IsAlloc(d, 
            Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
            $h) } 
        $IsAlloc(d, 
          Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
          $h))
     ==> $IsAlloc(ArrayTypeMagic.DList._h18(d), 
      Tclass.ArrayTypeMagic.Cell(ArrayTypeMagic.DList$T), 
      $h));

// Constructor literal
axiom (forall a#82#0#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Nil(Lit(a#82#0#0)) } 
  #ArrayTypeMagic.DList.Nil(Lit(a#82#0#0))
     == Lit(#ArrayTypeMagic.DList.Nil(a#82#0#0)));

function ArrayTypeMagic.DList._h18(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#83#0#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Nil(a#83#0#0) } 
  ArrayTypeMagic.DList._h18(#ArrayTypeMagic.DList.Nil(a#83#0#0)) == a#83#0#0);

// Inductive rank
axiom (forall a#84#0#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Nil(a#84#0#0) } 
  DtRank(a#84#0#0) < DtRank(#ArrayTypeMagic.DList.Nil(a#84#0#0)));

// Constructor function declaration
function #ArrayTypeMagic.DList.Cons(Box, Box, DatatypeType) : DatatypeType;

const unique ##ArrayTypeMagic.DList.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#85#0#0: Box, a#85#1#0: Box, a#85#2#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Cons(a#85#0#0, a#85#1#0, a#85#2#0) } 
  DatatypeCtorId(#ArrayTypeMagic.DList.Cons(a#85#0#0, a#85#1#0, a#85#2#0))
     == ##ArrayTypeMagic.DList.Cons);

function ArrayTypeMagic.DList.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.DList.Cons_q(d) } 
  ArrayTypeMagic.DList.Cons_q(d)
     <==> DatatypeCtorId(d) == ##ArrayTypeMagic.DList.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ArrayTypeMagic.DList.Cons_q(d) } 
  ArrayTypeMagic.DList.Cons_q(d)
     ==> (exists a#86#0#0: Box, a#86#1#0: Box, a#86#2#0: DatatypeType :: 
      d == #ArrayTypeMagic.DList.Cons(a#86#0#0, a#86#1#0, a#86#2#0)));

// Constructor $Is
axiom (forall ArrayTypeMagic.DList$T: Ty, 
    ArrayTypeMagic.DList$U: Ty, 
    a#87#0#0: Box, 
    a#87#1#0: Box, 
    a#87#2#0: DatatypeType :: 
  { $Is(#ArrayTypeMagic.DList.Cons(a#87#0#0, a#87#1#0, a#87#2#0), 
      Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U)) } 
  $Is(#ArrayTypeMagic.DList.Cons(a#87#0#0, a#87#1#0, a#87#2#0), 
      Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U))
     <==> $IsBox(a#87#0#0, ArrayTypeMagic.DList$T)
       && $IsBox(a#87#1#0, ArrayTypeMagic.DList$U)
       && $Is(a#87#2#0, 
        Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U)));

// Constructor $IsAlloc
axiom (forall ArrayTypeMagic.DList$T: Ty, 
    ArrayTypeMagic.DList$U: Ty, 
    a#88#0#0: Box, 
    a#88#1#0: Box, 
    a#88#2#0: DatatypeType, 
    $h: Heap :: 
  { $IsAlloc(#ArrayTypeMagic.DList.Cons(a#88#0#0, a#88#1#0, a#88#2#0), 
      Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ArrayTypeMagic.DList.Cons(a#88#0#0, a#88#1#0, a#88#2#0), 
        Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
        $h)
       <==> $IsAllocBox(a#88#0#0, ArrayTypeMagic.DList$T, $h)
         && $IsAllocBox(a#88#1#0, ArrayTypeMagic.DList$U, $h)
         && $IsAlloc(a#88#2#0, 
          Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
          $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.DList$T: Ty, $h: Heap :: 
  { $IsAllocBox(ArrayTypeMagic.DList._h19(d), ArrayTypeMagic.DList$T, $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.DList.Cons_q(d)
       && (exists ArrayTypeMagic.DList$U: Ty :: 
        { $IsAlloc(d, 
            Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
            $h) } 
        $IsAlloc(d, 
          Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
          $h))
     ==> $IsAllocBox(ArrayTypeMagic.DList._h19(d), ArrayTypeMagic.DList$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ArrayTypeMagic.DList$U: Ty, $h: Heap :: 
  { $IsAllocBox(ArrayTypeMagic.DList._h20(d), ArrayTypeMagic.DList$U, $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.DList.Cons_q(d)
       && (exists ArrayTypeMagic.DList$T: Ty :: 
        { $IsAlloc(d, 
            Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
            $h) } 
        $IsAlloc(d, 
          Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
          $h))
     ==> $IsAllocBox(ArrayTypeMagic.DList._h20(d), ArrayTypeMagic.DList$U, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, 
    ArrayTypeMagic.DList$T: Ty, 
    ArrayTypeMagic.DList$U: Ty, 
    $h: Heap :: 
  { $IsAlloc(ArrayTypeMagic.DList._h21(d), 
      Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
      $h) } 
  $IsGoodHeap($h)
       && 
      ArrayTypeMagic.DList.Cons_q(d)
       && $IsAlloc(d, 
        Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
        $h)
     ==> $IsAlloc(ArrayTypeMagic.DList._h21(d), 
      Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U), 
      $h));

// Constructor literal
axiom (forall a#89#0#0: Box, a#89#1#0: Box, a#89#2#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Cons(Lit(a#89#0#0), Lit(a#89#1#0), Lit(a#89#2#0)) } 
  #ArrayTypeMagic.DList.Cons(Lit(a#89#0#0), Lit(a#89#1#0), Lit(a#89#2#0))
     == Lit(#ArrayTypeMagic.DList.Cons(a#89#0#0, a#89#1#0, a#89#2#0)));

function ArrayTypeMagic.DList._h19(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#90#0#0: Box, a#90#1#0: Box, a#90#2#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Cons(a#90#0#0, a#90#1#0, a#90#2#0) } 
  ArrayTypeMagic.DList._h19(#ArrayTypeMagic.DList.Cons(a#90#0#0, a#90#1#0, a#90#2#0))
     == a#90#0#0);

// Inductive rank
axiom (forall a#91#0#0: Box, a#91#1#0: Box, a#91#2#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Cons(a#91#0#0, a#91#1#0, a#91#2#0) } 
  BoxRank(a#91#0#0)
     < DtRank(#ArrayTypeMagic.DList.Cons(a#91#0#0, a#91#1#0, a#91#2#0)));

function ArrayTypeMagic.DList._h20(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#92#0#0: Box, a#92#1#0: Box, a#92#2#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Cons(a#92#0#0, a#92#1#0, a#92#2#0) } 
  ArrayTypeMagic.DList._h20(#ArrayTypeMagic.DList.Cons(a#92#0#0, a#92#1#0, a#92#2#0))
     == a#92#1#0);

// Inductive rank
axiom (forall a#93#0#0: Box, a#93#1#0: Box, a#93#2#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Cons(a#93#0#0, a#93#1#0, a#93#2#0) } 
  BoxRank(a#93#1#0)
     < DtRank(#ArrayTypeMagic.DList.Cons(a#93#0#0, a#93#1#0, a#93#2#0)));

function ArrayTypeMagic.DList._h21(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#94#0#0: Box, a#94#1#0: Box, a#94#2#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Cons(a#94#0#0, a#94#1#0, a#94#2#0) } 
  ArrayTypeMagic.DList._h21(#ArrayTypeMagic.DList.Cons(a#94#0#0, a#94#1#0, a#94#2#0))
     == a#94#2#0);

// Inductive rank
axiom (forall a#95#0#0: Box, a#95#1#0: Box, a#95#2#0: DatatypeType :: 
  { #ArrayTypeMagic.DList.Cons(a#95#0#0, a#95#1#0, a#95#2#0) } 
  DtRank(a#95#2#0)
     < DtRank(#ArrayTypeMagic.DList.Cons(a#95#0#0, a#95#1#0, a#95#2#0)));

// Depth-one case-split function
function $IsA#ArrayTypeMagic.DList(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ArrayTypeMagic.DList(d) } 
  $IsA#ArrayTypeMagic.DList(d)
     ==> ArrayTypeMagic.DList.Nil_q(d) || ArrayTypeMagic.DList.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall ArrayTypeMagic.DList$T: Ty, ArrayTypeMagic.DList$U: Ty, d: DatatypeType :: 
  { ArrayTypeMagic.DList.Cons_q(d), $Is(d, Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U)) } 
    { ArrayTypeMagic.DList.Nil_q(d), $Is(d, Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U)) } 
  $Is(d, Tclass.ArrayTypeMagic.DList(ArrayTypeMagic.DList$T, ArrayTypeMagic.DList$U))
     ==> ArrayTypeMagic.DList.Nil_q(d) || ArrayTypeMagic.DList.Cons_q(d));

// Datatype extensional equality declaration
function ArrayTypeMagic.DList#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ArrayTypeMagic.DList.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.DList#Equal(a, b), ArrayTypeMagic.DList.Nil_q(a) } 
    { ArrayTypeMagic.DList#Equal(a, b), ArrayTypeMagic.DList.Nil_q(b) } 
  ArrayTypeMagic.DList.Nil_q(a) && ArrayTypeMagic.DList.Nil_q(b)
     ==> (ArrayTypeMagic.DList#Equal(a, b)
       <==> ArrayTypeMagic.Cell#Equal(ArrayTypeMagic.DList._h18(a), ArrayTypeMagic.DList._h18(b))));

// Datatype extensional equality definition: #ArrayTypeMagic.DList.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.DList#Equal(a, b), ArrayTypeMagic.DList.Cons_q(a) } 
    { ArrayTypeMagic.DList#Equal(a, b), ArrayTypeMagic.DList.Cons_q(b) } 
  ArrayTypeMagic.DList.Cons_q(a) && ArrayTypeMagic.DList.Cons_q(b)
     ==> (ArrayTypeMagic.DList#Equal(a, b)
       <==> ArrayTypeMagic.DList._h19(a) == ArrayTypeMagic.DList._h19(b)
         && ArrayTypeMagic.DList._h20(a) == ArrayTypeMagic.DList._h20(b)
         && ArrayTypeMagic.DList#Equal(ArrayTypeMagic.DList._h21(a), ArrayTypeMagic.DList._h21(b))));

// Datatype extensionality axiom: ArrayTypeMagic.DList
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ArrayTypeMagic.DList#Equal(a, b) } 
  ArrayTypeMagic.DList#Equal(a, b) <==> a == b);

const unique class.ArrayTypeMagic.DList: ClassName;

const unique class.ArrayTypeMagic.__default: ClassName;

function Tclass.ArrayTypeMagic.__default() : Ty;

const unique Tagclass.ArrayTypeMagic.__default: TyTag;

// Tclass.ArrayTypeMagic.__default Tag
axiom Tag(Tclass.ArrayTypeMagic.__default()) == Tagclass.ArrayTypeMagic.__default
   && TagFamily(Tclass.ArrayTypeMagic.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ArrayTypeMagic.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ArrayTypeMagic.__default()) } 
  $IsBox(bx, Tclass.ArrayTypeMagic.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ArrayTypeMagic.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ArrayTypeMagic.__default()) } 
  $Is($o, Tclass.ArrayTypeMagic.__default())
     <==> $o == null || dtype($o) == Tclass.ArrayTypeMagic.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ArrayTypeMagic.__default(), $h) } 
  $IsAlloc($o, Tclass.ArrayTypeMagic.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for ArrayTypeMagic._default.G
function ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0: Ty, $ly: LayerType, t#0: DatatypeType) : ref;

function ArrayTypeMagic.__default.G#canCall(ArrayTypeMagic._default.G$_T0: Ty, t#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall ArrayTypeMagic._default.G$_T0: Ty, $ly: LayerType, t#0: DatatypeType :: 
  { ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $LS($ly), t#0) } 
  ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $LS($ly), t#0)
     == ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $ly, t#0));

// fuel synonym axiom
axiom (forall ArrayTypeMagic._default.G$_T0: Ty, $ly: LayerType, t#0: DatatypeType :: 
  { ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, AsFuelBottom($ly), t#0) } 
  ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $ly, t#0)
     == ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $LZ, t#0));

// consequence axiom for ArrayTypeMagic.__default.G
axiom true
   ==> (forall ArrayTypeMagic._default.G$_T0: Ty, $ly: LayerType, t#0: DatatypeType :: 
    { ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $ly, t#0) } 
    ArrayTypeMagic.__default.G#canCall(ArrayTypeMagic._default.G$_T0, t#0)
         || $Is(t#0, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic._default.G$_T0))
       ==> $Is(ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $ly, t#0), 
        Tclass._System.array3(ArrayTypeMagic._default.G$_T0)));

function ArrayTypeMagic.__default.G#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for ArrayTypeMagic.__default.G
axiom (forall ArrayTypeMagic._default.G$_T0: Ty, $ly: LayerType, t#0: DatatypeType :: 
  { ArrayTypeMagic.__default.G#requires(ArrayTypeMagic._default.G$_T0, $ly, t#0) } 
  $Is(t#0, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic._default.G$_T0))
     ==> ArrayTypeMagic.__default.G#requires(ArrayTypeMagic._default.G$_T0, $ly, t#0)
       == true);

// definition axiom for ArrayTypeMagic.__default.G (revealed)
axiom true
   ==> (forall ArrayTypeMagic._default.G$_T0: Ty, $ly: LayerType, t#0: DatatypeType :: 
    { ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $LS($ly), t#0) } 
    ArrayTypeMagic.__default.G#canCall(ArrayTypeMagic._default.G$_T0, t#0)
         || $Is(t#0, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic._default.G$_T0))
       ==> (!ArrayTypeMagic.ArrayCubeTree.Leaf_q(t#0)
           ==> (var l#5 := ArrayTypeMagic.ArrayCubeTree._h5(t#0); 
            ArrayTypeMagic.__default.G#canCall(ArrayTypeMagic._default.G$_T0, l#5)))
         && ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $LS($ly), t#0)
           == (if ArrayTypeMagic.ArrayCubeTree.Leaf_q(t#0)
             then (var d#4 := ArrayTypeMagic.ArrayCubeTree._h4(t#0); d#4)
             else (var l#4 := ArrayTypeMagic.ArrayCubeTree._h5(t#0); 
              ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $ly, l#4))));

// definition axiom for ArrayTypeMagic.__default.G for all literals (revealed)
axiom true
   ==> (forall ArrayTypeMagic._default.G$_T0: Ty, $ly: LayerType, t#0: DatatypeType :: 
    {:weight 3} { ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $LS($ly), Lit(t#0)) } 
    ArrayTypeMagic.__default.G#canCall(ArrayTypeMagic._default.G$_T0, Lit(t#0))
         || $Is(t#0, Tclass.ArrayTypeMagic.ArrayCubeTree(ArrayTypeMagic._default.G$_T0))
       ==> (!Lit(ArrayTypeMagic.ArrayCubeTree.Leaf_q(Lit(t#0)))
           ==> (var l#7 := Lit(ArrayTypeMagic.ArrayCubeTree._h5(Lit(t#0))); 
            ArrayTypeMagic.__default.G#canCall(ArrayTypeMagic._default.G$_T0, l#7)))
         && ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $LS($ly), Lit(t#0))
           == (if ArrayTypeMagic.ArrayCubeTree.Leaf_q(Lit(t#0))
             then (var d#6 := Lit(ArrayTypeMagic.ArrayCubeTree._h4(Lit(t#0))); d#6)
             else (var l#6 := Lit(ArrayTypeMagic.ArrayCubeTree._h5(Lit(t#0))); 
              Lit(ArrayTypeMagic.__default.G(ArrayTypeMagic._default.G$_T0, $LS($ly), l#6)))));

const #$MyType: Ty;

const unique class.ParseGenerics.MyType: ClassName;

// Constructor function declaration
function #ParseGenerics.List.Nil() : DatatypeType;

const unique ##ParseGenerics.List.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#ParseGenerics.List.Nil()) == ##ParseGenerics.List.Nil;

function ParseGenerics.List.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ParseGenerics.List.Nil_q(d) } 
  ParseGenerics.List.Nil_q(d) <==> DatatypeCtorId(d) == ##ParseGenerics.List.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ParseGenerics.List.Nil_q(d) } 
  ParseGenerics.List.Nil_q(d) ==> d == #ParseGenerics.List.Nil());

function Tclass.ParseGenerics.List(Ty) : Ty;

const unique Tagclass.ParseGenerics.List: TyTag;

// Tclass.ParseGenerics.List Tag
axiom (forall ParseGenerics.List$Y: Ty :: 
  { Tclass.ParseGenerics.List(ParseGenerics.List$Y) } 
  Tag(Tclass.ParseGenerics.List(ParseGenerics.List$Y))
       == Tagclass.ParseGenerics.List
     && TagFamily(Tclass.ParseGenerics.List(ParseGenerics.List$Y)) == tytagFamily$List);

// Tclass.ParseGenerics.List injectivity 0
axiom (forall ParseGenerics.List$Y: Ty :: 
  { Tclass.ParseGenerics.List(ParseGenerics.List$Y) } 
  Tclass.ParseGenerics.List_0(Tclass.ParseGenerics.List(ParseGenerics.List$Y))
     == ParseGenerics.List$Y);

function Tclass.ParseGenerics.List_0(Ty) : Ty;

// Box/unbox axiom for Tclass.ParseGenerics.List
axiom (forall ParseGenerics.List$Y: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.ParseGenerics.List(ParseGenerics.List$Y)) } 
  $IsBox(bx, Tclass.ParseGenerics.List(ParseGenerics.List$Y))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.ParseGenerics.List(ParseGenerics.List$Y)));

// Constructor $Is
axiom (forall ParseGenerics.List$Y: Ty :: 
  { $Is(#ParseGenerics.List.Nil(), Tclass.ParseGenerics.List(ParseGenerics.List$Y)) } 
  $Is(#ParseGenerics.List.Nil(), Tclass.ParseGenerics.List(ParseGenerics.List$Y)));

// Constructor $IsAlloc
axiom (forall ParseGenerics.List$Y: Ty, $h: Heap :: 
  { $IsAlloc(#ParseGenerics.List.Nil(), Tclass.ParseGenerics.List(ParseGenerics.List$Y), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#ParseGenerics.List.Nil(), Tclass.ParseGenerics.List(ParseGenerics.List$Y), $h));

// Constructor literal
axiom #ParseGenerics.List.Nil() == Lit(#ParseGenerics.List.Nil());

// Constructor function declaration
function #ParseGenerics.List.Cons(Box, DatatypeType) : DatatypeType;

const unique ##ParseGenerics.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: DatatypeType :: 
  { #ParseGenerics.List.Cons(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#ParseGenerics.List.Cons(a#5#0#0, a#5#1#0))
     == ##ParseGenerics.List.Cons);

function ParseGenerics.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { ParseGenerics.List.Cons_q(d) } 
  ParseGenerics.List.Cons_q(d) <==> DatatypeCtorId(d) == ##ParseGenerics.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { ParseGenerics.List.Cons_q(d) } 
  ParseGenerics.List.Cons_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: DatatypeType :: 
      d == #ParseGenerics.List.Cons(a#6#0#0, a#6#1#0)));

// Constructor $Is
axiom (forall ParseGenerics.List$Y: Ty, a#7#0#0: Box, a#7#1#0: DatatypeType :: 
  { $Is(#ParseGenerics.List.Cons(a#7#0#0, a#7#1#0), 
      Tclass.ParseGenerics.List(ParseGenerics.List$Y)) } 
  $Is(#ParseGenerics.List.Cons(a#7#0#0, a#7#1#0), 
      Tclass.ParseGenerics.List(ParseGenerics.List$Y))
     <==> $IsBox(a#7#0#0, ParseGenerics.List$Y)
       && $Is(a#7#1#0, Tclass.ParseGenerics.List(ParseGenerics.List$Y)));

// Constructor $IsAlloc
axiom (forall ParseGenerics.List$Y: Ty, a#8#0#0: Box, a#8#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#ParseGenerics.List.Cons(a#8#0#0, a#8#1#0), 
      Tclass.ParseGenerics.List(ParseGenerics.List$Y), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#ParseGenerics.List.Cons(a#8#0#0, a#8#1#0), 
        Tclass.ParseGenerics.List(ParseGenerics.List$Y), 
        $h)
       <==> $IsAllocBox(a#8#0#0, ParseGenerics.List$Y, $h)
         && $IsAlloc(a#8#1#0, Tclass.ParseGenerics.List(ParseGenerics.List$Y), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ParseGenerics.List$Y: Ty, $h: Heap :: 
  { $IsAllocBox(ParseGenerics.List._h22(d), ParseGenerics.List$Y, $h) } 
  $IsGoodHeap($h)
       && 
      ParseGenerics.List.Cons_q(d)
       && $IsAlloc(d, Tclass.ParseGenerics.List(ParseGenerics.List$Y), $h)
     ==> $IsAllocBox(ParseGenerics.List._h22(d), ParseGenerics.List$Y, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, ParseGenerics.List$Y: Ty, $h: Heap :: 
  { $IsAlloc(ParseGenerics.List._h23(d), Tclass.ParseGenerics.List(ParseGenerics.List$Y), $h) } 
  $IsGoodHeap($h)
       && 
      ParseGenerics.List.Cons_q(d)
       && $IsAlloc(d, Tclass.ParseGenerics.List(ParseGenerics.List$Y), $h)
     ==> $IsAlloc(ParseGenerics.List._h23(d), Tclass.ParseGenerics.List(ParseGenerics.List$Y), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType :: 
  { #ParseGenerics.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #ParseGenerics.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#ParseGenerics.List.Cons(a#9#0#0, a#9#1#0)));

function ParseGenerics.List._h22(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType :: 
  { #ParseGenerics.List.Cons(a#10#0#0, a#10#1#0) } 
  ParseGenerics.List._h22(#ParseGenerics.List.Cons(a#10#0#0, a#10#1#0))
     == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType :: 
  { #ParseGenerics.List.Cons(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#ParseGenerics.List.Cons(a#11#0#0, a#11#1#0)));

function ParseGenerics.List._h23(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType :: 
  { #ParseGenerics.List.Cons(a#12#0#0, a#12#1#0) } 
  ParseGenerics.List._h23(#ParseGenerics.List.Cons(a#12#0#0, a#12#1#0))
     == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: DatatypeType :: 
  { #ParseGenerics.List.Cons(a#13#0#0, a#13#1#0) } 
  DtRank(a#13#1#0) < DtRank(#ParseGenerics.List.Cons(a#13#0#0, a#13#1#0)));

// Depth-one case-split function
function $IsA#ParseGenerics.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#ParseGenerics.List(d) } 
  $IsA#ParseGenerics.List(d)
     ==> ParseGenerics.List.Nil_q(d) || ParseGenerics.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall ParseGenerics.List$Y: Ty, d: DatatypeType :: 
  { ParseGenerics.List.Cons_q(d), $Is(d, Tclass.ParseGenerics.List(ParseGenerics.List$Y)) } 
    { ParseGenerics.List.Nil_q(d), $Is(d, Tclass.ParseGenerics.List(ParseGenerics.List$Y)) } 
  $Is(d, Tclass.ParseGenerics.List(ParseGenerics.List$Y))
     ==> ParseGenerics.List.Nil_q(d) || ParseGenerics.List.Cons_q(d));

// Datatype extensional equality declaration
function ParseGenerics.List#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #ParseGenerics.List.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ParseGenerics.List#Equal(a, b), ParseGenerics.List.Nil_q(a) } 
    { ParseGenerics.List#Equal(a, b), ParseGenerics.List.Nil_q(b) } 
  ParseGenerics.List.Nil_q(a) && ParseGenerics.List.Nil_q(b)
     ==> (ParseGenerics.List#Equal(a, b) <==> true));

// Datatype extensional equality definition: #ParseGenerics.List.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ParseGenerics.List#Equal(a, b), ParseGenerics.List.Cons_q(a) } 
    { ParseGenerics.List#Equal(a, b), ParseGenerics.List.Cons_q(b) } 
  ParseGenerics.List.Cons_q(a) && ParseGenerics.List.Cons_q(b)
     ==> (ParseGenerics.List#Equal(a, b)
       <==> ParseGenerics.List._h22(a) == ParseGenerics.List._h22(b)
         && ParseGenerics.List#Equal(ParseGenerics.List._h23(a), ParseGenerics.List._h23(b))));

// Datatype extensionality axiom: ParseGenerics.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { ParseGenerics.List#Equal(a, b) } 
  ParseGenerics.List#Equal(a, b) <==> a == b);

const unique class.ParseGenerics.List: ClassName;

const unique class.ParseGenerics.__default: ClassName;

function Tclass.ParseGenerics.__default() : Ty;

const unique Tagclass.ParseGenerics.__default: TyTag;

// Tclass.ParseGenerics.__default Tag
axiom Tag(Tclass.ParseGenerics.__default()) == Tagclass.ParseGenerics.__default
   && TagFamily(Tclass.ParseGenerics.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.ParseGenerics.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.ParseGenerics.__default()) } 
  $IsBox(bx, Tclass.ParseGenerics.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.ParseGenerics.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.ParseGenerics.__default()) } 
  $Is($o, Tclass.ParseGenerics.__default())
     <==> $o == null || dtype($o) == Tclass.ParseGenerics.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.ParseGenerics.__default(), $h) } 
  $IsAlloc($o, Tclass.ParseGenerics.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for ParseGenerics._default.F
function ParseGenerics.__default.F(ParseGenerics._default.F$X: Ty, x#0: Box) : int;

function ParseGenerics.__default.F#canCall(ParseGenerics._default.F$X: Ty, x#0: Box) : bool;

// consequence axiom for ParseGenerics.__default.F
axiom true
   ==> (forall ParseGenerics._default.F$X: Ty, x#0: Box :: 
    { ParseGenerics.__default.F(ParseGenerics._default.F$X, x#0) } 
    ParseGenerics.__default.F#canCall(ParseGenerics._default.F$X, x#0)
         || $IsBox(x#0, ParseGenerics._default.F$X)
       ==> true);

function ParseGenerics.__default.F#requires(Ty, Box) : bool;

// #requires axiom for ParseGenerics.__default.F
axiom (forall ParseGenerics._default.F$X: Ty, x#0: Box :: 
  { ParseGenerics.__default.F#requires(ParseGenerics._default.F$X, x#0) } 
  $IsBox(x#0, ParseGenerics._default.F$X)
     ==> ParseGenerics.__default.F#requires(ParseGenerics._default.F$X, x#0) == true);

// function declaration for ParseGenerics._default.Many
function ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0: Ty, $ly: LayerType, n#0: DatatypeType) : int;

function ParseGenerics.__default.Many#canCall(ParseGenerics._default.Many$_T0: Ty, n#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall ParseGenerics._default.Many$_T0: Ty, $ly: LayerType, n#0: DatatypeType :: 
  { ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $LS($ly), n#0) } 
  ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $LS($ly), n#0)
     == ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $ly, n#0));

// fuel synonym axiom
axiom (forall ParseGenerics._default.Many$_T0: Ty, $ly: LayerType, n#0: DatatypeType :: 
  { ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, AsFuelBottom($ly), n#0) } 
  ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $ly, n#0)
     == ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $LZ, n#0));

// consequence axiom for ParseGenerics.__default.Many
axiom true
   ==> (forall ParseGenerics._default.Many$_T0: Ty, $ly: LayerType, n#0: DatatypeType :: 
    { ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $ly, n#0) } 
    ParseGenerics.__default.Many#canCall(ParseGenerics._default.Many$_T0, n#0)
         || $Is(n#0, Tclass.ParseGenerics.List(ParseGenerics._default.Many$_T0))
       ==> true);

function ParseGenerics.__default.Many#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for ParseGenerics.__default.Many
axiom (forall ParseGenerics._default.Many$_T0: Ty, $ly: LayerType, n#0: DatatypeType :: 
  { ParseGenerics.__default.Many#requires(ParseGenerics._default.Many$_T0, $ly, n#0) } 
  $Is(n#0, Tclass.ParseGenerics.List(ParseGenerics._default.Many$_T0))
     ==> ParseGenerics.__default.Many#requires(ParseGenerics._default.Many$_T0, $ly, n#0)
       == true);

// definition axiom for ParseGenerics.__default.Many (revealed)
axiom true
   ==> (forall ParseGenerics._default.Many$_T0: Ty, $ly: LayerType, n#0: DatatypeType :: 
    { ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $LS($ly), n#0) } 
    ParseGenerics.__default.Many#canCall(ParseGenerics._default.Many$_T0, n#0)
         || $Is(n#0, Tclass.ParseGenerics.List(ParseGenerics._default.Many$_T0))
       ==> (!ParseGenerics.List.Nil_q(n#0)
           ==> (var tail#5 := ParseGenerics.List._h23(n#0); 
            ParseGenerics.__default.Many#canCall(ParseGenerics._default.Many$_T0, tail#5)))
         && ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $LS($ly), n#0)
           == (if ParseGenerics.List.Nil_q(n#0)
             then 18
             else (var tail#4 := ParseGenerics.List._h23(n#0); 
              ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $ly, tail#4))));

// definition axiom for ParseGenerics.__default.Many for all literals (revealed)
axiom true
   ==> (forall ParseGenerics._default.Many$_T0: Ty, $ly: LayerType, n#0: DatatypeType :: 
    {:weight 3} { ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $LS($ly), Lit(n#0)) } 
    ParseGenerics.__default.Many#canCall(ParseGenerics._default.Many$_T0, Lit(n#0))
         || $Is(n#0, Tclass.ParseGenerics.List(ParseGenerics._default.Many$_T0))
       ==> (!Lit(ParseGenerics.List.Nil_q(Lit(n#0)))
           ==> (var tail#7 := Lit(ParseGenerics.List._h23(Lit(n#0))); 
            ParseGenerics.__default.Many#canCall(ParseGenerics._default.Many$_T0, tail#7)))
         && ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $LS($ly), Lit(n#0))
           == (if ParseGenerics.List.Nil_q(Lit(n#0))
             then 18
             else (var tail#6 := Lit(ParseGenerics.List._h23(Lit(n#0))); 
              LitInt(ParseGenerics.__default.Many(ParseGenerics._default.Many$_T0, $LS($ly), tail#6)))));

const unique class.TypeSubstitutionInModifiesClause.C?: ClassName;

function Tclass.TypeSubstitutionInModifiesClause.C?(Ty) : Ty;

const unique Tagclass.TypeSubstitutionInModifiesClause.C?: TyTag;

// Tclass.TypeSubstitutionInModifiesClause.C? Tag
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty :: 
  { Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T) } 
  Tag(Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T))
       == Tagclass.TypeSubstitutionInModifiesClause.C?
     && TagFamily(Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T))
       == tytagFamily$C);

// Tclass.TypeSubstitutionInModifiesClause.C? injectivity 0
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty :: 
  { Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T) } 
  Tclass.TypeSubstitutionInModifiesClause.C?_0(Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T))
     == TypeSubstitutionInModifiesClause.C$T);

function Tclass.TypeSubstitutionInModifiesClause.C?_0(Ty) : Ty;

// Box/unbox axiom for Tclass.TypeSubstitutionInModifiesClause.C?
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T)) } 
  $IsBox(bx, 
      Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, 
        Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T)));

// C: Class $Is
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty, $o: ref :: 
  { $Is($o, 
      Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T)) } 
  $Is($o, 
      Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T))
     <==> $o == null
       || dtype($o)
         == Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T));

// C: Class $IsAlloc
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty, $o: ref, $h: Heap :: 
  { $IsAlloc($o, 
      Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T), 
      $h) } 
  $IsAlloc($o, 
      Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T), 
      $h)
     <==> $o == null || read($h, $o, alloc));

function TypeSubstitutionInModifiesClause.C.Repr(TypeSubstitutionInModifiesClause.C$T: Ty, this: ref) : Set Box;

// C.Repr: Type axiom
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty, $o: ref :: 
  { TypeSubstitutionInModifiesClause.C.Repr(TypeSubstitutionInModifiesClause.C$T, $o) } 
  $Is(TypeSubstitutionInModifiesClause.C.Repr(TypeSubstitutionInModifiesClause.C$T, $o), 
    TSet(Tclass._System.object())));

// C.Repr: Allocation axiom
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty, $h: Heap, $o: ref :: 
  { TypeSubstitutionInModifiesClause.C.Repr(TypeSubstitutionInModifiesClause.C$T, $o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(TypeSubstitutionInModifiesClause.C.Repr(TypeSubstitutionInModifiesClause.C$T, $o), 
      TSet(Tclass._System.object()), 
      $h));

function Tclass.TypeSubstitutionInModifiesClause.C(Ty) : Ty;

const unique Tagclass.TypeSubstitutionInModifiesClause.C: TyTag;

// Tclass.TypeSubstitutionInModifiesClause.C Tag
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty :: 
  { Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T) } 
  Tag(Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T))
       == Tagclass.TypeSubstitutionInModifiesClause.C
     && TagFamily(Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T))
       == tytagFamily$C);

// Tclass.TypeSubstitutionInModifiesClause.C injectivity 0
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty :: 
  { Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T) } 
  Tclass.TypeSubstitutionInModifiesClause.C_0(Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T))
     == TypeSubstitutionInModifiesClause.C$T);

function Tclass.TypeSubstitutionInModifiesClause.C_0(Ty) : Ty;

// Box/unbox axiom for Tclass.TypeSubstitutionInModifiesClause.C
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty, bx: Box :: 
  { $IsBox(bx, 
      Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T)) } 
  $IsBox(bx, 
      Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T))
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, 
        Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T)));

// TypeSubstitutionInModifiesClause.C: subset type $Is
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty, c#0: ref :: 
  { $Is(c#0, 
      Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T)) } 
  $Is(c#0, 
      Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T))
     <==> $Is(c#0, 
        Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T))
       && c#0 != null);

// TypeSubstitutionInModifiesClause.C: subset type $IsAlloc
axiom (forall TypeSubstitutionInModifiesClause.C$T: Ty, c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, 
      Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T), 
      $h) } 
  $IsAlloc(c#0, 
      Tclass.TypeSubstitutionInModifiesClause.C(TypeSubstitutionInModifiesClause.C$T), 
      $h)
     <==> $IsAlloc(c#0, 
      Tclass.TypeSubstitutionInModifiesClause.C?(TypeSubstitutionInModifiesClause.C$T), 
      $h));

const unique class.TypeSubstitutionInModifiesClause.__default: ClassName;

function Tclass.TypeSubstitutionInModifiesClause.__default() : Ty;

const unique Tagclass.TypeSubstitutionInModifiesClause.__default: TyTag;

// Tclass.TypeSubstitutionInModifiesClause.__default Tag
axiom Tag(Tclass.TypeSubstitutionInModifiesClause.__default())
     == Tagclass.TypeSubstitutionInModifiesClause.__default
   && TagFamily(Tclass.TypeSubstitutionInModifiesClause.__default())
     == tytagFamily$_default;

// Box/unbox axiom for Tclass.TypeSubstitutionInModifiesClause.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TypeSubstitutionInModifiesClause.__default()) } 
  $IsBox(bx, Tclass.TypeSubstitutionInModifiesClause.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TypeSubstitutionInModifiesClause.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TypeSubstitutionInModifiesClause.__default()) } 
  $Is($o, Tclass.TypeSubstitutionInModifiesClause.__default())
     <==> $o == null || dtype($o) == Tclass.TypeSubstitutionInModifiesClause.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TypeSubstitutionInModifiesClause.__default(), $h) } 
  $IsAlloc($o, Tclass.TypeSubstitutionInModifiesClause.__default(), $h)
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

const unique tytagFamily$_#Func2: TyTagFamily;

const unique tytagFamily$_#PartialFunc2: TyTagFamily;

const unique tytagFamily$_#TotalFunc2: TyTagFamily;

const unique tytagFamily$array2: TyTagFamily;

const unique tytagFamily$array3: TyTagFamily;

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$SetTest: TyTagFamily;

const unique tytagFamily$SequenceTest: TyTagFamily;

const unique tytagFamily$CC: TyTagFamily;

const unique tytagFamily$CClient: TyTagFamily;

const unique tytagFamily$TyKn_C: TyTagFamily;

const unique tytagFamily$TyKn_K: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Pair: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$wrap: TyTagFamily;

const unique tytagFamily$wrap2: TyTagFamily;

const unique tytagFamily$ArrayCubeTree: TyTagFamily;

const unique tytagFamily$AnotherACT: TyTagFamily;

const unique tytagFamily$OneMoreACT: TyTagFamily;

const unique tytagFamily$Nat: TyTagFamily;

const unique tytagFamily$Cell: TyTagFamily;

const unique tytagFamily$DList: TyTagFamily;

const unique field$x: NameFamily;
