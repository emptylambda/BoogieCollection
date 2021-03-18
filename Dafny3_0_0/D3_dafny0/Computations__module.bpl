// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy -print:./Computations.bpl

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

// Constructor function declaration
function #_module.intlist.IntNil() : DatatypeType;

const unique ##_module.intlist.IntNil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.intlist.IntNil()) == ##_module.intlist.IntNil;

function _module.intlist.IntNil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.intlist.IntNil_q(d) } 
  _module.intlist.IntNil_q(d) <==> DatatypeCtorId(d) == ##_module.intlist.IntNil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.intlist.IntNil_q(d) } 
  _module.intlist.IntNil_q(d) ==> d == #_module.intlist.IntNil());

function Tclass._module.intlist() : Ty;

const unique Tagclass._module.intlist: TyTag;

// Tclass._module.intlist Tag
axiom Tag(Tclass._module.intlist()) == Tagclass._module.intlist
   && TagFamily(Tclass._module.intlist()) == tytagFamily$intlist;

// Box/unbox axiom for Tclass._module.intlist
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.intlist()) } 
  $IsBox(bx, Tclass._module.intlist())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.intlist()));

// Constructor $Is
axiom $Is(#_module.intlist.IntNil(), Tclass._module.intlist());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#_module.intlist.IntNil(), Tclass._module.intlist(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.intlist.IntNil(), Tclass._module.intlist(), $h));

// Constructor literal
axiom #_module.intlist.IntNil() == Lit(#_module.intlist.IntNil());

// Constructor function declaration
function #_module.intlist.IntCons(int, DatatypeType) : DatatypeType;

const unique ##_module.intlist.IntCons: DtCtorId;

// Constructor identifier
axiom (forall a#19#0#0: int, a#19#1#0: DatatypeType :: 
  { #_module.intlist.IntCons(a#19#0#0, a#19#1#0) } 
  DatatypeCtorId(#_module.intlist.IntCons(a#19#0#0, a#19#1#0))
     == ##_module.intlist.IntCons);

function _module.intlist.IntCons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.intlist.IntCons_q(d) } 
  _module.intlist.IntCons_q(d) <==> DatatypeCtorId(d) == ##_module.intlist.IntCons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.intlist.IntCons_q(d) } 
  _module.intlist.IntCons_q(d)
     ==> (exists a#20#0#0: int, a#20#1#0: DatatypeType :: 
      d == #_module.intlist.IntCons(a#20#0#0, a#20#1#0)));

// Constructor $Is
axiom (forall a#21#0#0: int, a#21#1#0: DatatypeType :: 
  { $Is(#_module.intlist.IntCons(a#21#0#0, a#21#1#0), Tclass._module.intlist()) } 
  $Is(#_module.intlist.IntCons(a#21#0#0, a#21#1#0), Tclass._module.intlist())
     <==> $Is(a#21#0#0, TInt) && $Is(a#21#1#0, Tclass._module.intlist()));

// Constructor $IsAlloc
axiom (forall a#22#0#0: int, a#22#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.intlist.IntCons(a#22#0#0, a#22#1#0), Tclass._module.intlist(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.intlist.IntCons(a#22#0#0, a#22#1#0), Tclass._module.intlist(), $h)
       <==> $IsAlloc(a#22#0#0, TInt, $h) && $IsAlloc(a#22#1#0, Tclass._module.intlist(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.intlist.head(d), TInt, $h) } 
  $IsGoodHeap($h)
       && 
      _module.intlist.IntCons_q(d)
       && $IsAlloc(d, Tclass._module.intlist(), $h)
     ==> $IsAlloc(_module.intlist.head(d), TInt, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.intlist.tail(d), Tclass._module.intlist(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.intlist.IntCons_q(d)
       && $IsAlloc(d, Tclass._module.intlist(), $h)
     ==> $IsAlloc(_module.intlist.tail(d), Tclass._module.intlist(), $h));

// Constructor literal
axiom (forall a#23#0#0: int, a#23#1#0: DatatypeType :: 
  { #_module.intlist.IntCons(LitInt(a#23#0#0), Lit(a#23#1#0)) } 
  #_module.intlist.IntCons(LitInt(a#23#0#0), Lit(a#23#1#0))
     == Lit(#_module.intlist.IntCons(a#23#0#0, a#23#1#0)));

function _module.intlist.head(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#24#0#0: int, a#24#1#0: DatatypeType :: 
  { #_module.intlist.IntCons(a#24#0#0, a#24#1#0) } 
  _module.intlist.head(#_module.intlist.IntCons(a#24#0#0, a#24#1#0)) == a#24#0#0);

function _module.intlist.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#25#0#0: int, a#25#1#0: DatatypeType :: 
  { #_module.intlist.IntCons(a#25#0#0, a#25#1#0) } 
  _module.intlist.tail(#_module.intlist.IntCons(a#25#0#0, a#25#1#0)) == a#25#1#0);

// Inductive rank
axiom (forall a#26#0#0: int, a#26#1#0: DatatypeType :: 
  { #_module.intlist.IntCons(a#26#0#0, a#26#1#0) } 
  DtRank(a#26#1#0) < DtRank(#_module.intlist.IntCons(a#26#0#0, a#26#1#0)));

// Depth-one case-split function
function $IsA#_module.intlist(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.intlist(d) } 
  $IsA#_module.intlist(d)
     ==> _module.intlist.IntNil_q(d) || _module.intlist.IntCons_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.intlist.IntCons_q(d), $Is(d, Tclass._module.intlist()) } 
    { _module.intlist.IntNil_q(d), $Is(d, Tclass._module.intlist()) } 
  $Is(d, Tclass._module.intlist())
     ==> _module.intlist.IntNil_q(d) || _module.intlist.IntCons_q(d));

// Datatype extensional equality declaration
function _module.intlist#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.intlist.IntNil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.intlist#Equal(a, b), _module.intlist.IntNil_q(a) } 
    { _module.intlist#Equal(a, b), _module.intlist.IntNil_q(b) } 
  _module.intlist.IntNil_q(a) && _module.intlist.IntNil_q(b)
     ==> (_module.intlist#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.intlist.IntCons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.intlist#Equal(a, b), _module.intlist.IntCons_q(a) } 
    { _module.intlist#Equal(a, b), _module.intlist.IntCons_q(b) } 
  _module.intlist.IntCons_q(a) && _module.intlist.IntCons_q(b)
     ==> (_module.intlist#Equal(a, b)
       <==> _module.intlist.head(a) == _module.intlist.head(b)
         && _module.intlist#Equal(_module.intlist.tail(a), _module.intlist.tail(b))));

// Datatype extensionality axiom: _module.intlist
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.intlist#Equal(a, b) } 
  _module.intlist#Equal(a, b) <==> a == b);

const unique class._module.intlist: ClassName;

// Constructor function declaration
function #_module.list.Nil() : DatatypeType;

const unique ##_module.list.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#_module.list.Nil()) == ##_module.list.Nil;

function _module.list.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.list.Nil_q(d) } 
  _module.list.Nil_q(d) <==> DatatypeCtorId(d) == ##_module.list.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.list.Nil_q(d) } 
  _module.list.Nil_q(d) ==> d == #_module.list.Nil());

function Tclass._module.list(Ty) : Ty;

const unique Tagclass._module.list: TyTag;

// Tclass._module.list Tag
axiom (forall _module.list$A: Ty :: 
  { Tclass._module.list(_module.list$A) } 
  Tag(Tclass._module.list(_module.list$A)) == Tagclass._module.list
     && TagFamily(Tclass._module.list(_module.list$A)) == tytagFamily$list);

// Tclass._module.list injectivity 0
axiom (forall _module.list$A: Ty :: 
  { Tclass._module.list(_module.list$A) } 
  Tclass._module.list_0(Tclass._module.list(_module.list$A)) == _module.list$A);

function Tclass._module.list_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.list
axiom (forall _module.list$A: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.list(_module.list$A)) } 
  $IsBox(bx, Tclass._module.list(_module.list$A))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.list(_module.list$A)));

// Constructor $Is
axiom (forall _module.list$A: Ty :: 
  { $Is(#_module.list.Nil(), Tclass._module.list(_module.list$A)) } 
  $Is(#_module.list.Nil(), Tclass._module.list(_module.list$A)));

// Constructor $IsAlloc
axiom (forall _module.list$A: Ty, $h: Heap :: 
  { $IsAlloc(#_module.list.Nil(), Tclass._module.list(_module.list$A), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#_module.list.Nil(), Tclass._module.list(_module.list$A), $h));

// Constructor literal
axiom #_module.list.Nil() == Lit(#_module.list.Nil());

// Constructor function declaration
function #_module.list.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.list.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#32#0#0: Box, a#32#1#0: DatatypeType :: 
  { #_module.list.Cons(a#32#0#0, a#32#1#0) } 
  DatatypeCtorId(#_module.list.Cons(a#32#0#0, a#32#1#0)) == ##_module.list.Cons);

function _module.list.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.list.Cons_q(d) } 
  _module.list.Cons_q(d) <==> DatatypeCtorId(d) == ##_module.list.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.list.Cons_q(d) } 
  _module.list.Cons_q(d)
     ==> (exists a#33#0#0: Box, a#33#1#0: DatatypeType :: 
      d == #_module.list.Cons(a#33#0#0, a#33#1#0)));

// Constructor $Is
axiom (forall _module.list$A: Ty, a#34#0#0: Box, a#34#1#0: DatatypeType :: 
  { $Is(#_module.list.Cons(a#34#0#0, a#34#1#0), Tclass._module.list(_module.list$A)) } 
  $Is(#_module.list.Cons(a#34#0#0, a#34#1#0), Tclass._module.list(_module.list$A))
     <==> $IsBox(a#34#0#0, _module.list$A)
       && $Is(a#34#1#0, Tclass._module.list(_module.list$A)));

// Constructor $IsAlloc
axiom (forall _module.list$A: Ty, a#35#0#0: Box, a#35#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.list.Cons(a#35#0#0, a#35#1#0), Tclass._module.list(_module.list$A), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.list.Cons(a#35#0#0, a#35#1#0), Tclass._module.list(_module.list$A), $h)
       <==> $IsAllocBox(a#35#0#0, _module.list$A, $h)
         && $IsAlloc(a#35#1#0, Tclass._module.list(_module.list$A), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.list$A: Ty, $h: Heap :: 
  { $IsAllocBox(_module.list.head(d), _module.list$A, $h) } 
  $IsGoodHeap($h)
       && 
      _module.list.Cons_q(d)
       && $IsAlloc(d, Tclass._module.list(_module.list$A), $h)
     ==> $IsAllocBox(_module.list.head(d), _module.list$A, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.list$A: Ty, $h: Heap :: 
  { $IsAlloc(_module.list.tail(d), Tclass._module.list(_module.list$A), $h) } 
  $IsGoodHeap($h)
       && 
      _module.list.Cons_q(d)
       && $IsAlloc(d, Tclass._module.list(_module.list$A), $h)
     ==> $IsAlloc(_module.list.tail(d), Tclass._module.list(_module.list$A), $h));

// Constructor literal
axiom (forall a#36#0#0: Box, a#36#1#0: DatatypeType :: 
  { #_module.list.Cons(Lit(a#36#0#0), Lit(a#36#1#0)) } 
  #_module.list.Cons(Lit(a#36#0#0), Lit(a#36#1#0))
     == Lit(#_module.list.Cons(a#36#0#0, a#36#1#0)));

function _module.list.head(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#37#0#0: Box, a#37#1#0: DatatypeType :: 
  { #_module.list.Cons(a#37#0#0, a#37#1#0) } 
  _module.list.head(#_module.list.Cons(a#37#0#0, a#37#1#0)) == a#37#0#0);

// Inductive rank
axiom (forall a#38#0#0: Box, a#38#1#0: DatatypeType :: 
  { #_module.list.Cons(a#38#0#0, a#38#1#0) } 
  BoxRank(a#38#0#0) < DtRank(#_module.list.Cons(a#38#0#0, a#38#1#0)));

function _module.list.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#39#0#0: Box, a#39#1#0: DatatypeType :: 
  { #_module.list.Cons(a#39#0#0, a#39#1#0) } 
  _module.list.tail(#_module.list.Cons(a#39#0#0, a#39#1#0)) == a#39#1#0);

// Inductive rank
axiom (forall a#40#0#0: Box, a#40#1#0: DatatypeType :: 
  { #_module.list.Cons(a#40#0#0, a#40#1#0) } 
  DtRank(a#40#1#0) < DtRank(#_module.list.Cons(a#40#0#0, a#40#1#0)));

// Depth-one case-split function
function $IsA#_module.list(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.list(d) } 
  $IsA#_module.list(d) ==> _module.list.Nil_q(d) || _module.list.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.list$A: Ty, d: DatatypeType :: 
  { _module.list.Cons_q(d), $Is(d, Tclass._module.list(_module.list$A)) } 
    { _module.list.Nil_q(d), $Is(d, Tclass._module.list(_module.list$A)) } 
  $Is(d, Tclass._module.list(_module.list$A))
     ==> _module.list.Nil_q(d) || _module.list.Cons_q(d));

// Datatype extensional equality declaration
function _module.list#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.list.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.list#Equal(a, b), _module.list.Nil_q(a) } 
    { _module.list#Equal(a, b), _module.list.Nil_q(b) } 
  _module.list.Nil_q(a) && _module.list.Nil_q(b)
     ==> (_module.list#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.list.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.list#Equal(a, b), _module.list.Cons_q(a) } 
    { _module.list#Equal(a, b), _module.list.Cons_q(b) } 
  _module.list.Cons_q(a) && _module.list.Cons_q(b)
     ==> (_module.list#Equal(a, b)
       <==> _module.list.head(a) == _module.list.head(b)
         && _module.list#Equal(_module.list.tail(a), _module.list.tail(b))));

// Datatype extensionality axiom: _module.list
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.list#Equal(a, b) } 
  _module.list#Equal(a, b) <==> a == b);

const unique class._module.list: ClassName;

// Constructor function declaration
function #_module.exp.Plus(DatatypeType, DatatypeType) : DatatypeType;

const unique ##_module.exp.Plus: DtCtorId;

// Constructor identifier
axiom (forall a#41#0#0: DatatypeType, a#41#1#0: DatatypeType :: 
  { #_module.exp.Plus(a#41#0#0, a#41#1#0) } 
  DatatypeCtorId(#_module.exp.Plus(a#41#0#0, a#41#1#0)) == ##_module.exp.Plus);

function _module.exp.Plus_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.exp.Plus_q(d) } 
  _module.exp.Plus_q(d) <==> DatatypeCtorId(d) == ##_module.exp.Plus);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.exp.Plus_q(d) } 
  _module.exp.Plus_q(d)
     ==> (exists a#42#0#0: DatatypeType, a#42#1#0: DatatypeType :: 
      d == #_module.exp.Plus(a#42#0#0, a#42#1#0)));

function Tclass._module.exp() : Ty;

const unique Tagclass._module.exp: TyTag;

// Tclass._module.exp Tag
axiom Tag(Tclass._module.exp()) == Tagclass._module.exp
   && TagFamily(Tclass._module.exp()) == tytagFamily$exp;

// Box/unbox axiom for Tclass._module.exp
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.exp()) } 
  $IsBox(bx, Tclass._module.exp())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.exp()));

// Constructor $Is
axiom (forall a#43#0#0: DatatypeType, a#43#1#0: DatatypeType :: 
  { $Is(#_module.exp.Plus(a#43#0#0, a#43#1#0), Tclass._module.exp()) } 
  $Is(#_module.exp.Plus(a#43#0#0, a#43#1#0), Tclass._module.exp())
     <==> $Is(a#43#0#0, Tclass._module.exp()) && $Is(a#43#1#0, Tclass._module.exp()));

// Constructor $IsAlloc
axiom (forall a#44#0#0: DatatypeType, a#44#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.exp.Plus(a#44#0#0, a#44#1#0), Tclass._module.exp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.exp.Plus(a#44#0#0, a#44#1#0), Tclass._module.exp(), $h)
       <==> $IsAlloc(a#44#0#0, Tclass._module.exp(), $h)
         && $IsAlloc(a#44#1#0, Tclass._module.exp(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.exp.e1(d), Tclass._module.exp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.exp.Plus_q(d)
       && $IsAlloc(d, Tclass._module.exp(), $h)
     ==> $IsAlloc(_module.exp.e1(d), Tclass._module.exp(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.exp.e2(d), Tclass._module.exp(), $h) } 
  $IsGoodHeap($h)
       && 
      _module.exp.Plus_q(d)
       && $IsAlloc(d, Tclass._module.exp(), $h)
     ==> $IsAlloc(_module.exp.e2(d), Tclass._module.exp(), $h));

// Constructor literal
axiom (forall a#45#0#0: DatatypeType, a#45#1#0: DatatypeType :: 
  { #_module.exp.Plus(Lit(a#45#0#0), Lit(a#45#1#0)) } 
  #_module.exp.Plus(Lit(a#45#0#0), Lit(a#45#1#0))
     == Lit(#_module.exp.Plus(a#45#0#0, a#45#1#0)));

function _module.exp.e1(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#46#0#0: DatatypeType, a#46#1#0: DatatypeType :: 
  { #_module.exp.Plus(a#46#0#0, a#46#1#0) } 
  _module.exp.e1(#_module.exp.Plus(a#46#0#0, a#46#1#0)) == a#46#0#0);

// Inductive rank
axiom (forall a#47#0#0: DatatypeType, a#47#1#0: DatatypeType :: 
  { #_module.exp.Plus(a#47#0#0, a#47#1#0) } 
  DtRank(a#47#0#0) < DtRank(#_module.exp.Plus(a#47#0#0, a#47#1#0)));

function _module.exp.e2(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#48#0#0: DatatypeType, a#48#1#0: DatatypeType :: 
  { #_module.exp.Plus(a#48#0#0, a#48#1#0) } 
  _module.exp.e2(#_module.exp.Plus(a#48#0#0, a#48#1#0)) == a#48#1#0);

// Inductive rank
axiom (forall a#49#0#0: DatatypeType, a#49#1#0: DatatypeType :: 
  { #_module.exp.Plus(a#49#0#0, a#49#1#0) } 
  DtRank(a#49#1#0) < DtRank(#_module.exp.Plus(a#49#0#0, a#49#1#0)));

// Constructor function declaration
function #_module.exp.Num(int) : DatatypeType;

const unique ##_module.exp.Num: DtCtorId;

// Constructor identifier
axiom (forall a#50#0#0: int :: 
  { #_module.exp.Num(a#50#0#0) } 
  DatatypeCtorId(#_module.exp.Num(a#50#0#0)) == ##_module.exp.Num);

function _module.exp.Num_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.exp.Num_q(d) } 
  _module.exp.Num_q(d) <==> DatatypeCtorId(d) == ##_module.exp.Num);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.exp.Num_q(d) } 
  _module.exp.Num_q(d)
     ==> (exists a#51#0#0: int :: d == #_module.exp.Num(a#51#0#0)));

// Constructor $Is
axiom (forall a#52#0#0: int :: 
  { $Is(#_module.exp.Num(a#52#0#0), Tclass._module.exp()) } 
  $Is(#_module.exp.Num(a#52#0#0), Tclass._module.exp()) <==> $Is(a#52#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#53#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.exp.Num(a#53#0#0), Tclass._module.exp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.exp.Num(a#53#0#0), Tclass._module.exp(), $h)
       <==> $IsAlloc(a#53#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.exp.n(d), TInt, $h) } 
  $IsGoodHeap($h) && _module.exp.Num_q(d) && $IsAlloc(d, Tclass._module.exp(), $h)
     ==> $IsAlloc(_module.exp.n(d), TInt, $h));

// Constructor literal
axiom (forall a#54#0#0: int :: 
  { #_module.exp.Num(LitInt(a#54#0#0)) } 
  #_module.exp.Num(LitInt(a#54#0#0)) == Lit(#_module.exp.Num(a#54#0#0)));

function _module.exp.n(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#55#0#0: int :: 
  { #_module.exp.Num(a#55#0#0) } 
  _module.exp.n(#_module.exp.Num(a#55#0#0)) == a#55#0#0);

// Constructor function declaration
function #_module.exp.Var(int) : DatatypeType;

const unique ##_module.exp.Var: DtCtorId;

// Constructor identifier
axiom (forall a#56#0#0: int :: 
  { #_module.exp.Var(a#56#0#0) } 
  DatatypeCtorId(#_module.exp.Var(a#56#0#0)) == ##_module.exp.Var);

function _module.exp.Var_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.exp.Var_q(d) } 
  _module.exp.Var_q(d) <==> DatatypeCtorId(d) == ##_module.exp.Var);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.exp.Var_q(d) } 
  _module.exp.Var_q(d)
     ==> (exists a#57#0#0: int :: d == #_module.exp.Var(a#57#0#0)));

// Constructor $Is
axiom (forall a#58#0#0: int :: 
  { $Is(#_module.exp.Var(a#58#0#0), Tclass._module.exp()) } 
  $Is(#_module.exp.Var(a#58#0#0), Tclass._module.exp()) <==> $Is(a#58#0#0, TInt));

// Constructor $IsAlloc
axiom (forall a#59#0#0: int, $h: Heap :: 
  { $IsAlloc(#_module.exp.Var(a#59#0#0), Tclass._module.exp(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.exp.Var(a#59#0#0), Tclass._module.exp(), $h)
       <==> $IsAlloc(a#59#0#0, TInt, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(_module.exp.x(d), TInt, $h) } 
  $IsGoodHeap($h) && _module.exp.Var_q(d) && $IsAlloc(d, Tclass._module.exp(), $h)
     ==> $IsAlloc(_module.exp.x(d), TInt, $h));

// Constructor literal
axiom (forall a#60#0#0: int :: 
  { #_module.exp.Var(LitInt(a#60#0#0)) } 
  #_module.exp.Var(LitInt(a#60#0#0)) == Lit(#_module.exp.Var(a#60#0#0)));

function _module.exp.x(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#61#0#0: int :: 
  { #_module.exp.Var(a#61#0#0) } 
  _module.exp.x(#_module.exp.Var(a#61#0#0)) == a#61#0#0);

// Depth-one case-split function
function $IsA#_module.exp(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.exp(d) } 
  $IsA#_module.exp(d)
     ==> _module.exp.Plus_q(d) || _module.exp.Num_q(d) || _module.exp.Var_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { _module.exp.Var_q(d), $Is(d, Tclass._module.exp()) } 
    { _module.exp.Num_q(d), $Is(d, Tclass._module.exp()) } 
    { _module.exp.Plus_q(d), $Is(d, Tclass._module.exp()) } 
  $Is(d, Tclass._module.exp())
     ==> _module.exp.Plus_q(d) || _module.exp.Num_q(d) || _module.exp.Var_q(d));

// Datatype extensional equality declaration
function _module.exp#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.exp.Plus
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.exp#Equal(a, b), _module.exp.Plus_q(a) } 
    { _module.exp#Equal(a, b), _module.exp.Plus_q(b) } 
  _module.exp.Plus_q(a) && _module.exp.Plus_q(b)
     ==> (_module.exp#Equal(a, b)
       <==> _module.exp#Equal(_module.exp.e1(a), _module.exp.e1(b))
         && _module.exp#Equal(_module.exp.e2(a), _module.exp.e2(b))));

// Datatype extensional equality definition: #_module.exp.Num
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.exp#Equal(a, b), _module.exp.Num_q(a) } 
    { _module.exp#Equal(a, b), _module.exp.Num_q(b) } 
  _module.exp.Num_q(a) && _module.exp.Num_q(b)
     ==> (_module.exp#Equal(a, b) <==> _module.exp.n(a) == _module.exp.n(b)));

// Datatype extensional equality definition: #_module.exp.Var
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.exp#Equal(a, b), _module.exp.Var_q(a) } 
    { _module.exp#Equal(a, b), _module.exp.Var_q(b) } 
  _module.exp.Var_q(a) && _module.exp.Var_q(b)
     ==> (_module.exp#Equal(a, b) <==> _module.exp.x(a) == _module.exp.x(b)));

// Datatype extensionality axiom: _module.exp
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.exp#Equal(a, b) } 
  _module.exp#Equal(a, b) <==> a == b);

const unique class._module.exp: ClassName;

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

// function declaration for _module._default.fact6
function _module.__default.fact6(n#0: int) : int;

function _module.__default.fact6#canCall(n#0: int) : bool;

// consequence axiom for _module.__default.fact6
axiom 5 <= $FunctionContextHeight
   ==> (forall n#0: int :: 
    { _module.__default.fact6(n#0) } 
    _module.__default.fact6#canCall(n#0)
         || (5 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> LitInt(0) <= _module.__default.fact6(n#0));

function _module.__default.fact6#requires(int) : bool;

// #requires axiom for _module.__default.fact6
axiom (forall n#0: int :: 
  { _module.__default.fact6#requires(n#0) } 
  LitInt(0) <= n#0 ==> _module.__default.fact6#requires(n#0) == true);

// definition axiom for _module.__default.fact6 (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall n#0: int :: 
    { _module.__default.fact6(n#0) } 
    _module.__default.fact6#canCall(n#0)
         || (5 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> _module.__default.fact#canCall(n#0 + 6)
         && _module.__default.fact6(n#0) == _module.__default.fact($LS($LZ), n#0 + 6));

// definition axiom for _module.__default.fact6 for all literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> (forall n#0: int :: 
    {:weight 3} { _module.__default.fact6(LitInt(n#0)) } 
    _module.__default.fact6#canCall(LitInt(n#0))
         || (5 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> _module.__default.fact#canCall(LitInt(n#0 + 6))
         && _module.__default.fact6(LitInt(n#0))
           == LitInt(_module.__default.fact($LS($LZ), LitInt(n#0 + 6))));

procedure CheckWellformed$$_module.__default.fact6(n#0: int where LitInt(0) <= n#0);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.fact6(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function fact6
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(4,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.fact6(n#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert $Is(n#0 + 6, Tclass._System.nat());
        ##n#0 := n#0 + 6;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.fact#canCall(n#0 + 6);
        assume _module.__default.fact6(n#0) == _module.__default.fact($LS($LZ), n#0 + 6);
        assume _module.__default.fact#canCall(n#0 + 6);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.fact6(n#0), Tclass._System.nat());
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.fact
function _module.__default.fact($ly: LayerType, n#0: int) : int;

function _module.__default.fact#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.fact($LS($ly), n#0) } 
  _module.__default.fact($LS($ly), n#0) == _module.__default.fact($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.fact(AsFuelBottom($ly), n#0) } 
  _module.__default.fact($ly, n#0) == _module.__default.fact($LZ, n#0));

// consequence axiom for _module.__default.fact
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.fact($ly, n#0) } 
    _module.__default.fact#canCall(n#0)
         || (4 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> LitInt(0) <= _module.__default.fact($ly, n#0));

function _module.__default.fact#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.fact
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.fact#requires($ly, n#0) } 
  LitInt(0) <= n#0 ==> _module.__default.fact#requires($ly, n#0) == true);

// definition axiom for _module.__default.fact (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.fact($LS($ly), n#0) } 
    _module.__default.fact#canCall(n#0)
         || (4 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> _module.__default.fact#canCall(n#0 - 1))
         && _module.__default.fact($LS($ly), n#0)
           == (if n#0 == LitInt(0) then 1 else Mul(n#0, _module.__default.fact($ly, n#0 - 1))));

// definition axiom for _module.__default.fact for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.fact($LS($ly), LitInt(n#0)) } 
    _module.__default.fact#canCall(LitInt(n#0))
         || (4 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0) ==> _module.__default.fact#canCall(LitInt(n#0 - 1)))
         && _module.__default.fact($LS($ly), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then 1
             else Mul(LitInt(n#0), LitInt(_module.__default.fact($LS($ly), LitInt(n#0 - 1))))));

procedure CheckWellformed$$_module.__default.fact(n#0: int where LitInt(0) <= n#0);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.fact(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function fact
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(9,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.fact($LS($LZ), n#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == LitInt(0))
        {
            assert $Is(LitInt(1), Tclass._System.nat());
            assume _module.__default.fact($LS($LZ), n#0) == LitInt(1);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.fact($LS($LZ), n#0), Tclass._System.nat());
        }
        else
        {
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.fact#canCall(n#0 - 1);
            assert $Is(Mul(n#0, _module.__default.fact($LS($LZ), n#0 - 1)), Tclass._System.nat());
            assume _module.__default.fact($LS($LZ), n#0)
               == Mul(n#0, _module.__default.fact($LS($LZ), n#0 - 1));
            assume _module.__default.fact#canCall(n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.fact($LS($LZ), n#0), Tclass._System.nat());
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.compute__fact6();
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.compute__fact6()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;

    // AddMethodImpl: compute_fact6, CheckWellformed$$_module.__default.compute__fact6
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(13,13): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(14,17): post-state"} true;
    assert $Is(LitInt(6), Tclass._System.nat());
    ##n#0 := LitInt(6);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.fact#canCall(LitInt(6));
    assume LitInt(_module.__default.fact($LS($LZ), LitInt(6))) == LitInt(720);
}



procedure Call$$_module.__default.compute__fact6();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.fact#canCall(LitInt(6));
  ensures LitInt(_module.__default.fact($LS($LS($LZ)), LitInt(6))) == LitInt(720);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__fact6() returns ($_reverifyPost: bool);
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.fact#canCall(LitInt(6));
  ensures LitInt(_module.__default.fact($LS($LS($LZ)), LitInt(6))) == LitInt(720);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__fact6() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_fact6, Impl$$_module.__default.compute__fact6
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(15,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.compute__fact6__plus();
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.compute__fact6__plus()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;

    // AddMethodImpl: compute_fact6_plus, CheckWellformed$$_module.__default.compute__fact6__plus
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(17,13): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(18,18): post-state"} true;
    assert $Is(LitInt(0), Tclass._System.nat());
    ##n#0 := LitInt(0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.fact6#canCall(LitInt(0));
    assume LitInt(_module.__default.fact6(LitInt(0))) == LitInt(720);
}



procedure Call$$_module.__default.compute__fact6__plus();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.fact6#canCall(LitInt(0));
  ensures LitInt(_module.__default.fact6(LitInt(0))) == LitInt(720);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__fact6__plus() returns ($_reverifyPost: bool);
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.fact6#canCall(LitInt(0));
  ensures LitInt(_module.__default.fact6(LitInt(0))) == LitInt(720);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__fact6__plus() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_fact6_plus, Impl$$_module.__default.compute__fact6__plus
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(19,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.intsize
function _module.__default.intsize($ly: LayerType, l#0: DatatypeType) : int;

function _module.__default.intsize#canCall(l#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.intsize($LS($ly), l#0) } 
  _module.__default.intsize($LS($ly), l#0) == _module.__default.intsize($ly, l#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.intsize(AsFuelBottom($ly), l#0) } 
  _module.__default.intsize($ly, l#0) == _module.__default.intsize($LZ, l#0));

// consequence axiom for _module.__default.intsize
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType :: 
    { _module.__default.intsize($ly, l#0) } 
    _module.__default.intsize#canCall(l#0)
         || (6 != $FunctionContextHeight && $Is(l#0, Tclass._module.intlist()))
       ==> LitInt(0) <= _module.__default.intsize($ly, l#0));

function _module.__default.intsize#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.intsize
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.intsize#requires($ly, l#0) } 
  $Is(l#0, Tclass._module.intlist())
     ==> _module.__default.intsize#requires($ly, l#0) == true);

// definition axiom for _module.__default.intsize (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType :: 
    { _module.__default.intsize($LS($ly), l#0) } 
    _module.__default.intsize#canCall(l#0)
         || (6 != $FunctionContextHeight && $Is(l#0, Tclass._module.intlist()))
       ==> (!_module.intlist.IntNil_q(l#0)
           ==> _module.__default.intsize#canCall(_module.intlist.tail(l#0)))
         && _module.__default.intsize($LS($ly), l#0)
           == (if _module.intlist.IntNil_q(l#0)
             then 0
             else 1 + _module.__default.intsize($ly, _module.intlist.tail(l#0))));

// definition axiom for _module.__default.intsize for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType :: 
    {:weight 3} { _module.__default.intsize($LS($ly), Lit(l#0)) } 
    _module.__default.intsize#canCall(Lit(l#0))
         || (6 != $FunctionContextHeight && $Is(l#0, Tclass._module.intlist()))
       ==> (!Lit(_module.intlist.IntNil_q(Lit(l#0)))
           ==> _module.__default.intsize#canCall(Lit(_module.intlist.tail(Lit(l#0)))))
         && _module.__default.intsize($LS($ly), Lit(l#0))
           == (if _module.intlist.IntNil_q(Lit(l#0))
             then 0
             else 1 + _module.__default.intsize($LS($ly), Lit(_module.intlist.tail(Lit(l#0))))));

procedure CheckWellformed$$_module.__default.intsize(l#0: DatatypeType where $Is(l#0, Tclass._module.intlist()));
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.intsize(l#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function intsize
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(23,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.intsize($LS($LZ), l#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (_module.intlist.IntNil_q(l#0))
        {
            assert $Is(LitInt(0), Tclass._System.nat());
            assume _module.__default.intsize($LS($LZ), l#0) == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.intsize($LS($LZ), l#0), Tclass._System.nat());
        }
        else
        {
            assert _module.intlist.IntCons_q(l#0);
            ##l#0 := _module.intlist.tail(l#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.intlist(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##l#0) < DtRank(l#0);
            assume _module.__default.intsize#canCall(_module.intlist.tail(l#0));
            assert $Is(1 + _module.__default.intsize($LS($LZ), _module.intlist.tail(l#0)), 
              Tclass._System.nat());
            assume _module.__default.intsize($LS($LZ), l#0)
               == 1 + _module.__default.intsize($LS($LZ), _module.intlist.tail(l#0));
            assume _module.__default.intsize#canCall(_module.intlist.tail(l#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.intsize($LS($LZ), l#0), Tclass._System.nat());
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.intapp
function _module.__default.intapp($ly: LayerType, a#0: DatatypeType, b#0: DatatypeType) : DatatypeType;

function _module.__default.intapp#canCall(a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.intapp($LS($ly), a#0, b#0) } 
  _module.__default.intapp($LS($ly), a#0, b#0)
     == _module.__default.intapp($ly, a#0, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.intapp(AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.intapp($ly, a#0, b#0)
     == _module.__default.intapp($LZ, a#0, b#0));

// consequence axiom for _module.__default.intapp
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.intapp($ly, a#0, b#0) } 
    _module.__default.intapp#canCall(a#0, b#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.intlist())
           && $Is(b#0, Tclass._module.intlist()))
       ==> $Is(_module.__default.intapp($ly, a#0, b#0), Tclass._module.intlist()));

function _module.__default.intapp#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.intapp
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.intapp#requires($ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.intlist()) && $Is(b#0, Tclass._module.intlist())
     ==> _module.__default.intapp#requires($ly, a#0, b#0) == true);

// definition axiom for _module.__default.intapp (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.intapp($LS($ly), a#0, b#0) } 
    _module.__default.intapp#canCall(a#0, b#0)
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.intlist())
           && $Is(b#0, Tclass._module.intlist()))
       ==> (!_module.intlist.IntNil_q(a#0)
           ==> _module.__default.intapp#canCall(_module.intlist.tail(a#0), b#0))
         && _module.__default.intapp($LS($ly), a#0, b#0)
           == (if _module.intlist.IntNil_q(a#0)
             then b#0
             else #_module.intlist.IntCons(_module.intlist.head(a#0), 
              _module.__default.intapp($ly, _module.intlist.tail(a#0), b#0))));

// definition axiom for _module.__default.intapp for all literals (revealed)
axiom 7 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.intapp($LS($ly), Lit(a#0), Lit(b#0)) } 
    _module.__default.intapp#canCall(Lit(a#0), Lit(b#0))
         || (7 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.intlist())
           && $Is(b#0, Tclass._module.intlist()))
       ==> (!Lit(_module.intlist.IntNil_q(Lit(a#0)))
           ==> _module.__default.intapp#canCall(Lit(_module.intlist.tail(Lit(a#0))), Lit(b#0)))
         && _module.__default.intapp($LS($ly), Lit(a#0), Lit(b#0))
           == (if _module.intlist.IntNil_q(Lit(a#0))
             then b#0
             else #_module.intlist.IntCons(LitInt(_module.intlist.head(Lit(a#0))), 
              Lit(_module.__default.intapp($LS($ly), Lit(_module.intlist.tail(Lit(a#0))), Lit(b#0))))));

procedure CheckWellformed$$_module.__default.intapp(a#0: DatatypeType where $Is(a#0, Tclass._module.intlist()), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.intlist()));
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.intapp(a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function intapp
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(27,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.intapp($LS($LZ), a#0, b#0), Tclass._module.intlist());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (_module.intlist.IntNil_q(a#0))
        {
            assume _module.__default.intapp($LS($LZ), a#0, b#0) == b#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.intapp($LS($LZ), a#0, b#0), Tclass._module.intlist());
        }
        else
        {
            assert _module.intlist.IntCons_q(a#0);
            assert _module.intlist.IntCons_q(a#0);
            ##a#0 := _module.intlist.tail(a#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.intlist(), $Heap);
            ##b#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.intlist(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##a#0) < DtRank(a#0)
               || (DtRank(##a#0) == DtRank(a#0) && DtRank(##b#0) < DtRank(b#0));
            assume _module.__default.intapp#canCall(_module.intlist.tail(a#0), b#0);
            assume _module.__default.intapp($LS($LZ), a#0, b#0)
               == #_module.intlist.IntCons(_module.intlist.head(a#0), 
                _module.__default.intapp($LS($LZ), _module.intlist.tail(a#0), b#0));
            assume _module.__default.intapp#canCall(_module.intlist.tail(a#0), b#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.intapp($LS($LZ), a#0, b#0), Tclass._module.intlist());
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.compute__intappsize();
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__intappsize();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.intapp#canCall(Lit(#_module.intlist.IntCons(LitInt(1), 
          Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
      Lit(#_module.intlist.IntCons(LitInt(3), 
          Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))
     && _module.__default.intsize#canCall(Lit(_module.__default.intapp($LS($LZ), 
          Lit(#_module.intlist.IntCons(LitInt(1), 
              Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
          Lit(#_module.intlist.IntCons(LitInt(3), 
              Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))));
  ensures LitInt(_module.__default.intsize($LS($LS($LZ)), 
        Lit(_module.__default.intapp($LS($LS($LZ)), 
            Lit(#_module.intlist.IntCons(LitInt(1), 
                Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
            Lit(#_module.intlist.IntCons(LitInt(3), 
                Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil())))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__intappsize() returns ($_reverifyPost: bool);
  free requires 23 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.intapp#canCall(Lit(#_module.intlist.IntCons(LitInt(1), 
          Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
      Lit(#_module.intlist.IntCons(LitInt(3), 
          Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))
     && _module.__default.intsize#canCall(Lit(_module.__default.intapp($LS($LZ), 
          Lit(#_module.intlist.IntCons(LitInt(1), 
              Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
          Lit(#_module.intlist.IntCons(LitInt(3), 
              Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))));
  ensures LitInt(_module.__default.intsize($LS($LS($LZ)), 
        Lit(_module.__default.intapp($LS($LS($LZ)), 
            Lit(#_module.intlist.IntCons(LitInt(1), 
                Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
            Lit(#_module.intlist.IntCons(LitInt(3), 
                Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil())))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__intappsize() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_intappsize, Impl$$_module.__default.compute__intappsize
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(33,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.compute__intsize4();
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__intsize4();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.intsize#canCall(Lit(#_module.intlist.IntCons(LitInt(1), 
        Lit(#_module.intlist.IntCons(LitInt(2), 
            Lit(#_module.intlist.IntCons(LitInt(3), 
                Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))))));
  ensures LitInt(_module.__default.intsize($LS($LS($LZ)), 
        Lit(#_module.intlist.IntCons(LitInt(1), 
            Lit(#_module.intlist.IntCons(LitInt(2), 
                Lit(#_module.intlist.IntCons(LitInt(3), 
                    Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil())))))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__intsize4() returns ($_reverifyPost: bool);
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.intsize#canCall(Lit(#_module.intlist.IntCons(LitInt(1), 
        Lit(#_module.intlist.IntCons(LitInt(2), 
            Lit(#_module.intlist.IntCons(LitInt(3), 
                Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))))));
  ensures LitInt(_module.__default.intsize($LS($LS($LZ)), 
        Lit(#_module.intlist.IntCons(LitInt(1), 
            Lit(#_module.intlist.IntCons(LitInt(2), 
                Lit(#_module.intlist.IntCons(LitInt(3), 
                    Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil())))))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__intsize4() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_intsize4, Impl$$_module.__default.compute__intsize4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(37,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.cintsize
function _module.__default.cintsize($ly: LayerType, l#0: DatatypeType) : int;

function _module.__default.cintsize#canCall(l#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.cintsize($LS($ly), l#0) } 
  _module.__default.cintsize($LS($ly), l#0)
     == _module.__default.cintsize($ly, l#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.cintsize(AsFuelBottom($ly), l#0) } 
  _module.__default.cintsize($ly, l#0) == _module.__default.cintsize($LZ, l#0));

// consequence axiom for _module.__default.cintsize
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType :: 
    { _module.__default.cintsize($ly, l#0) } 
    _module.__default.cintsize#canCall(l#0)
         || (8 != $FunctionContextHeight && $Is(l#0, Tclass._module.intlist()))
       ==> LitInt(0) <= _module.__default.cintsize($ly, l#0));

function _module.__default.cintsize#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.cintsize
axiom (forall $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.cintsize#requires($ly, l#0) } 
  $Is(l#0, Tclass._module.intlist())
     ==> _module.__default.cintsize#requires($ly, l#0) == true);

// definition axiom for _module.__default.cintsize (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType :: 
    { _module.__default.cintsize($LS($ly), l#0) } 
    _module.__default.cintsize#canCall(l#0)
         || (8 != $FunctionContextHeight && $Is(l#0, Tclass._module.intlist()))
       ==> (!_module.intlist.IntNil_q(l#0)
           ==> (var tl#1 := _module.intlist.tail(l#0); 
            _module.__default.cintsize#canCall(tl#1)))
         && _module.__default.cintsize($LS($ly), l#0)
           == (if _module.intlist.IntNil_q(l#0)
             then 0
             else (var tl#0 := _module.intlist.tail(l#0); 
              (var hd#0 := _module.intlist.head(l#0); 
                1 + _module.__default.cintsize($ly, tl#0)))));

// definition axiom for _module.__default.cintsize for all literals (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, l#0: DatatypeType :: 
    {:weight 3} { _module.__default.cintsize($LS($ly), Lit(l#0)) } 
    _module.__default.cintsize#canCall(Lit(l#0))
         || (8 != $FunctionContextHeight && $Is(l#0, Tclass._module.intlist()))
       ==> (!Lit(_module.intlist.IntNil_q(Lit(l#0)))
           ==> (var tl#3 := Lit(_module.intlist.tail(Lit(l#0))); 
            _module.__default.cintsize#canCall(tl#3)))
         && _module.__default.cintsize($LS($ly), Lit(l#0))
           == (if _module.intlist.IntNil_q(Lit(l#0))
             then 0
             else (var tl#2 := Lit(_module.intlist.tail(Lit(l#0))); 
              (var hd#2 := LitInt(_module.intlist.head(Lit(l#0))); 
                LitInt(1 + _module.__default.cintsize($LS($ly), tl#2))))));

procedure CheckWellformed$$_module.__default.cintsize(l#0: DatatypeType where $Is(l#0, Tclass._module.intlist()));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.cintsize(l#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var tl#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var hd#Z#0: int;
  var let#1#0#0: int;
  var ##l#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function cintsize
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(39,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.cintsize($LS($LZ), l#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (l#0 == #_module.intlist.IntNil())
        {
            assert $Is(LitInt(0), Tclass._System.nat());
            assume _module.__default.cintsize($LS($LZ), l#0) == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.cintsize($LS($LZ), l#0), Tclass._System.nat());
        }
        else if (l#0 == #_module.intlist.IntCons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.intlist());
            havoc tl#Z#0;
            assume $Is(tl#Z#0, Tclass._module.intlist());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.intlist());
            assume tl#Z#0 == let#0#0#0;
            havoc hd#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume hd#Z#0 == let#1#0#0;
            ##l#0 := tl#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.intlist(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##l#0) < DtRank(l#0);
            assume _module.__default.cintsize#canCall(tl#Z#0);
            assert $Is(1 + _module.__default.cintsize($LS($LZ), tl#Z#0), Tclass._System.nat());
            assume _module.__default.cintsize($LS($LZ), l#0)
               == 1 + _module.__default.cintsize($LS($LZ), tl#Z#0);
            assume _module.__default.cintsize#canCall(tl#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.cintsize($LS($LZ), l#0), Tclass._System.nat());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.cintapp
function _module.__default.cintapp($ly: LayerType, a#0: DatatypeType, b#0: DatatypeType) : DatatypeType;

function _module.__default.cintapp#canCall(a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.cintapp($LS($ly), a#0, b#0) } 
  _module.__default.cintapp($LS($ly), a#0, b#0)
     == _module.__default.cintapp($ly, a#0, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.cintapp(AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.cintapp($ly, a#0, b#0)
     == _module.__default.cintapp($LZ, a#0, b#0));

// consequence axiom for _module.__default.cintapp
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.cintapp($ly, a#0, b#0) } 
    _module.__default.cintapp#canCall(a#0, b#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.intlist())
           && $Is(b#0, Tclass._module.intlist()))
       ==> $Is(_module.__default.cintapp($ly, a#0, b#0), Tclass._module.intlist()));

function _module.__default.cintapp#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.cintapp
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.cintapp#requires($ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.intlist()) && $Is(b#0, Tclass._module.intlist())
     ==> _module.__default.cintapp#requires($ly, a#0, b#0) == true);

// definition axiom for _module.__default.cintapp (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.cintapp($LS($ly), a#0, b#0) } 
    _module.__default.cintapp#canCall(a#0, b#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.intlist())
           && $Is(b#0, Tclass._module.intlist()))
       ==> (!_module.intlist.IntNil_q(a#0)
           ==> (var tl#1 := _module.intlist.tail(a#0); 
            _module.__default.cintapp#canCall(tl#1, b#0)))
         && _module.__default.cintapp($LS($ly), a#0, b#0)
           == (if _module.intlist.IntNil_q(a#0)
             then b#0
             else (var tl#0 := _module.intlist.tail(a#0); 
              (var hd#0 := _module.intlist.head(a#0); 
                #_module.intlist.IntCons(hd#0, _module.__default.cintapp($ly, tl#0, b#0))))));

// definition axiom for _module.__default.cintapp for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    {:weight 3} { _module.__default.cintapp($LS($ly), Lit(a#0), Lit(b#0)) } 
    _module.__default.cintapp#canCall(Lit(a#0), Lit(b#0))
         || (9 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.intlist())
           && $Is(b#0, Tclass._module.intlist()))
       ==> (!Lit(_module.intlist.IntNil_q(Lit(a#0)))
           ==> (var tl#3 := Lit(_module.intlist.tail(Lit(a#0))); 
            _module.__default.cintapp#canCall(tl#3, Lit(b#0))))
         && _module.__default.cintapp($LS($ly), Lit(a#0), Lit(b#0))
           == (if _module.intlist.IntNil_q(Lit(a#0))
             then b#0
             else (var tl#2 := Lit(_module.intlist.tail(Lit(a#0))); 
              (var hd#2 := LitInt(_module.intlist.head(Lit(a#0))); 
                Lit(#_module.intlist.IntCons(hd#2, Lit(_module.__default.cintapp($LS($ly), tl#2, Lit(b#0)))))))));

procedure CheckWellformed$$_module.__default.cintapp(a#0: DatatypeType where $Is(a#0, Tclass._module.intlist()), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.intlist()));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.cintapp(a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#0#0: int;
  var _mcc#1#0: DatatypeType;
  var tl#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var hd#Z#0: int;
  var let#1#0#0: int;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function cintapp
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(45,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.cintapp($LS($LZ), a#0, b#0), Tclass._module.intlist());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (a#0 == #_module.intlist.IntNil())
        {
            assume _module.__default.cintapp($LS($LZ), a#0, b#0) == b#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.cintapp($LS($LZ), a#0, b#0), Tclass._module.intlist());
        }
        else if (a#0 == #_module.intlist.IntCons(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#1#0, Tclass._module.intlist());
            havoc tl#Z#0;
            assume $Is(tl#Z#0, Tclass._module.intlist());
            assume let#0#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass._module.intlist());
            assume tl#Z#0 == let#0#0#0;
            havoc hd#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume hd#Z#0 == let#1#0#0;
            ##a#0 := tl#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.intlist(), $Heap);
            ##b#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.intlist(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##a#0) < DtRank(a#0)
               || (DtRank(##a#0) == DtRank(a#0) && DtRank(##b#0) < DtRank(b#0));
            assume _module.__default.cintapp#canCall(tl#Z#0, b#0);
            assume _module.__default.cintapp($LS($LZ), a#0, b#0)
               == #_module.intlist.IntCons(hd#Z#0, _module.__default.cintapp($LS($LZ), tl#Z#0, b#0));
            assume _module.__default.cintapp#canCall(tl#Z#0, b#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.cintapp($LS($LZ), a#0, b#0), Tclass._module.intlist());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.compute__cintappsize();
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__cintappsize();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cintapp#canCall(Lit(#_module.intlist.IntCons(LitInt(1), 
          Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
      Lit(#_module.intlist.IntCons(LitInt(3), 
          Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))
     && _module.__default.cintsize#canCall(Lit(_module.__default.cintapp($LS($LZ), 
          Lit(#_module.intlist.IntCons(LitInt(1), 
              Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
          Lit(#_module.intlist.IntCons(LitInt(3), 
              Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))));
  ensures LitInt(_module.__default.cintsize($LS($LS($LZ)), 
        Lit(_module.__default.cintapp($LS($LS($LZ)), 
            Lit(#_module.intlist.IntCons(LitInt(1), 
                Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
            Lit(#_module.intlist.IntCons(LitInt(3), 
                Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil())))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__cintappsize() returns ($_reverifyPost: bool);
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cintapp#canCall(Lit(#_module.intlist.IntCons(LitInt(1), 
          Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
      Lit(#_module.intlist.IntCons(LitInt(3), 
          Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))
     && _module.__default.cintsize#canCall(Lit(_module.__default.cintapp($LS($LZ), 
          Lit(#_module.intlist.IntCons(LitInt(1), 
              Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
          Lit(#_module.intlist.IntCons(LitInt(3), 
              Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))));
  ensures LitInt(_module.__default.cintsize($LS($LS($LZ)), 
        Lit(_module.__default.cintapp($LS($LS($LZ)), 
            Lit(#_module.intlist.IntCons(LitInt(1), 
                Lit(#_module.intlist.IntCons(LitInt(2), Lit(#_module.intlist.IntNil()))))), 
            Lit(#_module.intlist.IntCons(LitInt(3), 
                Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil())))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__cintappsize() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_cintappsize, Impl$$_module.__default.compute__cintappsize
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(53,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.compute__cintsize4();
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__cintsize4();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cintsize#canCall(Lit(#_module.intlist.IntCons(LitInt(1), 
        Lit(#_module.intlist.IntCons(LitInt(2), 
            Lit(#_module.intlist.IntCons(LitInt(3), 
                Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))))));
  ensures LitInt(_module.__default.cintsize($LS($LS($LZ)), 
        Lit(#_module.intlist.IntCons(LitInt(1), 
            Lit(#_module.intlist.IntCons(LitInt(2), 
                Lit(#_module.intlist.IntCons(LitInt(3), 
                    Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil())))))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__cintsize4() returns ($_reverifyPost: bool);
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cintsize#canCall(Lit(#_module.intlist.IntCons(LitInt(1), 
        Lit(#_module.intlist.IntCons(LitInt(2), 
            Lit(#_module.intlist.IntCons(LitInt(3), 
                Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil()))))))))));
  ensures LitInt(_module.__default.cintsize($LS($LS($LZ)), 
        Lit(#_module.intlist.IntCons(LitInt(1), 
            Lit(#_module.intlist.IntCons(LitInt(2), 
                Lit(#_module.intlist.IntCons(LitInt(3), 
                    Lit(#_module.intlist.IntCons(LitInt(4), Lit(#_module.intlist.IntNil())))))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__cintsize4() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_cintsize4, Impl$$_module.__default.compute__cintsize4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(57,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.size
function _module.__default.size(_module._default.size$_T0: Ty, $ly: LayerType, l#0: DatatypeType) : int;

function _module.__default.size#canCall(_module._default.size$_T0: Ty, l#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.size$_T0: Ty, $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.size(_module._default.size$_T0, $LS($ly), l#0) } 
  _module.__default.size(_module._default.size$_T0, $LS($ly), l#0)
     == _module.__default.size(_module._default.size$_T0, $ly, l#0));

// fuel synonym axiom
axiom (forall _module._default.size$_T0: Ty, $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.size(_module._default.size$_T0, AsFuelBottom($ly), l#0) } 
  _module.__default.size(_module._default.size$_T0, $ly, l#0)
     == _module.__default.size(_module._default.size$_T0, $LZ, l#0));

// consequence axiom for _module.__default.size
axiom 10 <= $FunctionContextHeight
   ==> (forall _module._default.size$_T0: Ty, $ly: LayerType, l#0: DatatypeType :: 
    { _module.__default.size(_module._default.size$_T0, $ly, l#0) } 
    _module.__default.size#canCall(_module._default.size$_T0, l#0)
         || (10 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.list(_module._default.size$_T0)))
       ==> LitInt(0) <= _module.__default.size(_module._default.size$_T0, $ly, l#0));

function _module.__default.size#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.size
axiom (forall _module._default.size$_T0: Ty, $ly: LayerType, l#0: DatatypeType :: 
  { _module.__default.size#requires(_module._default.size$_T0, $ly, l#0) } 
  $Is(l#0, Tclass._module.list(_module._default.size$_T0))
     ==> _module.__default.size#requires(_module._default.size$_T0, $ly, l#0) == true);

// definition axiom for _module.__default.size (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall _module._default.size$_T0: Ty, $ly: LayerType, l#0: DatatypeType :: 
    { _module.__default.size(_module._default.size$_T0, $LS($ly), l#0) } 
    _module.__default.size#canCall(_module._default.size$_T0, l#0)
         || (10 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.list(_module._default.size$_T0)))
       ==> (!_module.list.Nil_q(l#0)
           ==> _module.__default.size#canCall(_module._default.size$_T0, _module.list.tail(l#0)))
         && _module.__default.size(_module._default.size$_T0, $LS($ly), l#0)
           == (if _module.list.Nil_q(l#0)
             then 0
             else 1
               + _module.__default.size(_module._default.size$_T0, $ly, _module.list.tail(l#0))));

// definition axiom for _module.__default.size for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall _module._default.size$_T0: Ty, $ly: LayerType, l#0: DatatypeType :: 
    {:weight 3} { _module.__default.size(_module._default.size$_T0, $LS($ly), Lit(l#0)) } 
    _module.__default.size#canCall(_module._default.size$_T0, Lit(l#0))
         || (10 != $FunctionContextHeight
           && $Is(l#0, Tclass._module.list(_module._default.size$_T0)))
       ==> (!Lit(_module.list.Nil_q(Lit(l#0)))
           ==> _module.__default.size#canCall(_module._default.size$_T0, Lit(_module.list.tail(Lit(l#0)))))
         && _module.__default.size(_module._default.size$_T0, $LS($ly), Lit(l#0))
           == (if _module.list.Nil_q(Lit(l#0))
             then 0
             else 1
               + _module.__default.size(_module._default.size$_T0, $LS($ly), Lit(_module.list.tail(Lit(l#0))))));

procedure CheckWellformed$$_module.__default.size(_module._default.size$_T0: Ty, 
    l#0: DatatypeType where $Is(l#0, Tclass._module.list(_module._default.size$_T0)));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.size(_module._default.size$_T0: Ty, l#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##l#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function size
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(60,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.size(_module._default.size$_T0, $LS($LZ), l#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (_module.list.Nil_q(l#0))
        {
            assert $Is(LitInt(0), Tclass._System.nat());
            assume _module.__default.size(_module._default.size$_T0, $LS($LZ), l#0) == LitInt(0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.size(_module._default.size$_T0, $LS($LZ), l#0), 
              Tclass._System.nat());
        }
        else
        {
            assert _module.list.Cons_q(l#0);
            ##l#0 := _module.list.tail(l#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##l#0, Tclass._module.list(_module._default.size$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##l#0) < DtRank(l#0);
            assume _module.__default.size#canCall(_module._default.size$_T0, _module.list.tail(l#0));
            assert $Is(1
                 + _module.__default.size(_module._default.size$_T0, $LS($LZ), _module.list.tail(l#0)), 
              Tclass._System.nat());
            assume _module.__default.size(_module._default.size$_T0, $LS($LZ), l#0)
               == 1
                 + _module.__default.size(_module._default.size$_T0, $LS($LZ), _module.list.tail(l#0));
            assume _module.__default.size#canCall(_module._default.size$_T0, _module.list.tail(l#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.size(_module._default.size$_T0, $LS($LZ), l#0), 
              Tclass._System.nat());
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.app
function _module.__default.app(_module._default.app$_T0: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
   : DatatypeType;

function _module.__default.app#canCall(_module._default.app$_T0: Ty, a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.app$_T0: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.app(_module._default.app$_T0, $LS($ly), a#0, b#0) } 
  _module.__default.app(_module._default.app$_T0, $LS($ly), a#0, b#0)
     == _module.__default.app(_module._default.app$_T0, $ly, a#0, b#0));

// fuel synonym axiom
axiom (forall _module._default.app$_T0: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.app(_module._default.app$_T0, AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.app(_module._default.app$_T0, $ly, a#0, b#0)
     == _module.__default.app(_module._default.app$_T0, $LZ, a#0, b#0));

// consequence axiom for _module.__default.app
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.app$_T0: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.app(_module._default.app$_T0, $ly, a#0, b#0) } 
    _module.__default.app#canCall(_module._default.app$_T0, a#0, b#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.list(_module._default.app$_T0))
           && $Is(b#0, Tclass._module.list(_module._default.app$_T0)))
       ==> $Is(_module.__default.app(_module._default.app$_T0, $ly, a#0, b#0), 
        Tclass._module.list(_module._default.app$_T0)));

function _module.__default.app#requires(Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.app
axiom (forall _module._default.app$_T0: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.app#requires(_module._default.app$_T0, $ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.list(_module._default.app$_T0))
       && $Is(b#0, Tclass._module.list(_module._default.app$_T0))
     ==> _module.__default.app#requires(_module._default.app$_T0, $ly, a#0, b#0) == true);

// definition axiom for _module.__default.app (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.app$_T0: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.app(_module._default.app$_T0, $LS($ly), a#0, b#0) } 
    _module.__default.app#canCall(_module._default.app$_T0, a#0, b#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.list(_module._default.app$_T0))
           && $Is(b#0, Tclass._module.list(_module._default.app$_T0)))
       ==> (!_module.list.Nil_q(a#0)
           ==> _module.__default.app#canCall(_module._default.app$_T0, _module.list.tail(a#0), b#0))
         && _module.__default.app(_module._default.app$_T0, $LS($ly), a#0, b#0)
           == (if _module.list.Nil_q(a#0)
             then b#0
             else #_module.list.Cons(_module.list.head(a#0), 
              _module.__default.app(_module._default.app$_T0, $ly, _module.list.tail(a#0), b#0))));

// definition axiom for _module.__default.app for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall _module._default.app$_T0: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    {:weight 3} { _module.__default.app(_module._default.app$_T0, $LS($ly), Lit(a#0), Lit(b#0)) } 
    _module.__default.app#canCall(_module._default.app$_T0, Lit(a#0), Lit(b#0))
         || (11 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.list(_module._default.app$_T0))
           && $Is(b#0, Tclass._module.list(_module._default.app$_T0)))
       ==> (!Lit(_module.list.Nil_q(Lit(a#0)))
           ==> _module.__default.app#canCall(_module._default.app$_T0, Lit(_module.list.tail(Lit(a#0))), Lit(b#0)))
         && _module.__default.app(_module._default.app$_T0, $LS($ly), Lit(a#0), Lit(b#0))
           == (if _module.list.Nil_q(Lit(a#0))
             then b#0
             else #_module.list.Cons(Lit(_module.list.head(Lit(a#0))), 
              Lit(_module.__default.app(_module._default.app$_T0, $LS($ly), Lit(_module.list.tail(Lit(a#0))), Lit(b#0))))));

procedure CheckWellformed$$_module.__default.app(_module._default.app$_T0: Ty, 
    a#0: DatatypeType where $Is(a#0, Tclass._module.list(_module._default.app$_T0)), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.list(_module._default.app$_T0)));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.app(_module._default.app$_T0: Ty, a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function app
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(64,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.app(_module._default.app$_T0, $LS($LZ), a#0, b#0), 
          Tclass._module.list(_module._default.app$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (_module.list.Nil_q(a#0))
        {
            assume _module.__default.app(_module._default.app$_T0, $LS($LZ), a#0, b#0) == b#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.app(_module._default.app$_T0, $LS($LZ), a#0, b#0), 
              Tclass._module.list(_module._default.app$_T0));
        }
        else
        {
            assert _module.list.Cons_q(a#0);
            assert _module.list.Cons_q(a#0);
            ##a#0 := _module.list.tail(a#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#0, Tclass._module.list(_module._default.app$_T0), $Heap);
            ##b#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, Tclass._module.list(_module._default.app$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##a#0) < DtRank(a#0)
               || (DtRank(##a#0) == DtRank(a#0) && DtRank(##b#0) < DtRank(b#0));
            assume _module.__default.app#canCall(_module._default.app$_T0, _module.list.tail(a#0), b#0);
            assume _module.__default.app(_module._default.app$_T0, $LS($LZ), a#0, b#0)
               == #_module.list.Cons(_module.list.head(a#0), 
                _module.__default.app(_module._default.app$_T0, $LS($LZ), _module.list.tail(a#0), b#0));
            assume _module.__default.app#canCall(_module._default.app$_T0, _module.list.tail(a#0), b#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.app(_module._default.app$_T0, $LS($LZ), a#0, b#0), 
              Tclass._module.list(_module._default.app$_T0));
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.compute__size4();
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__size4();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.size#canCall(TInt, 
    Lit(#_module.list.Cons($Box(LitInt(1)), 
        Lit(#_module.list.Cons($Box(LitInt(2)), 
            Lit(#_module.list.Cons($Box(LitInt(3)), 
                Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil()))))))))));
  ensures LitInt(_module.__default.size(TInt, 
        $LS($LS($LZ)), 
        Lit(#_module.list.Cons($Box(LitInt(1)), 
            Lit(#_module.list.Cons($Box(LitInt(2)), 
                Lit(#_module.list.Cons($Box(LitInt(3)), 
                    Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil())))))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__size4() returns ($_reverifyPost: bool);
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.size#canCall(TInt, 
    Lit(#_module.list.Cons($Box(LitInt(1)), 
        Lit(#_module.list.Cons($Box(LitInt(2)), 
            Lit(#_module.list.Cons($Box(LitInt(3)), 
                Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil()))))))))));
  ensures LitInt(_module.__default.size(TInt, 
        $LS($LS($LZ)), 
        Lit(#_module.list.Cons($Box(LitInt(1)), 
            Lit(#_module.list.Cons($Box(LitInt(2)), 
                Lit(#_module.list.Cons($Box(LitInt(3)), 
                    Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil())))))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__size4() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_size4, Impl$$_module.__default.compute__size4
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(70,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.compute__size4__cons();
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__size4__cons();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.size#canCall(Tclass._module.intlist(), 
    Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
        Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
            Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
                Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), Lit(#_module.list.Nil()))))))))));
  ensures LitInt(_module.__default.size(Tclass._module.intlist(), 
        $LS($LS($LZ)), 
        Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
            Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
                Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
                    Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), Lit(#_module.list.Nil())))))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__size4__cons() returns ($_reverifyPost: bool);
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.size#canCall(Tclass._module.intlist(), 
    Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
        Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
            Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
                Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), Lit(#_module.list.Nil()))))))))));
  ensures LitInt(_module.__default.size(Tclass._module.intlist(), 
        $LS($LS($LZ)), 
        Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
            Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
                Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), 
                    Lit(#_module.list.Cons($Box(Lit(#_module.intlist.IntNil())), Lit(#_module.list.Nil())))))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__size4__cons() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_size4_cons, Impl$$_module.__default.compute__size4__cons
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(74,0): initial state"} true;
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.compute__appsize();
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__appsize();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.app#canCall(TInt, 
      Lit(#_module.list.Cons($Box(LitInt(1)), 
          Lit(#_module.list.Cons($Box(LitInt(2)), Lit(#_module.list.Nil()))))), 
      Lit(#_module.list.Cons($Box(LitInt(3)), 
          Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil()))))))
     && _module.__default.size#canCall(TInt, 
      Lit(_module.__default.app(TInt, 
          $LS($LZ), 
          Lit(#_module.list.Cons($Box(LitInt(1)), 
              Lit(#_module.list.Cons($Box(LitInt(2)), Lit(#_module.list.Nil()))))), 
          Lit(#_module.list.Cons($Box(LitInt(3)), 
              Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil()))))))));
  ensures LitInt(_module.__default.size(TInt, 
        $LS($LS($LZ)), 
        Lit(_module.__default.app(TInt, 
            $LS($LS($LZ)), 
            Lit(#_module.list.Cons($Box(LitInt(1)), 
                Lit(#_module.list.Cons($Box(LitInt(2)), Lit(#_module.list.Nil()))))), 
            Lit(#_module.list.Cons($Box(LitInt(3)), 
                Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil())))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__appsize() returns ($_reverifyPost: bool);
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.app#canCall(TInt, 
      Lit(#_module.list.Cons($Box(LitInt(1)), 
          Lit(#_module.list.Cons($Box(LitInt(2)), Lit(#_module.list.Nil()))))), 
      Lit(#_module.list.Cons($Box(LitInt(3)), 
          Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil()))))))
     && _module.__default.size#canCall(TInt, 
      Lit(_module.__default.app(TInt, 
          $LS($LZ), 
          Lit(#_module.list.Cons($Box(LitInt(1)), 
              Lit(#_module.list.Cons($Box(LitInt(2)), Lit(#_module.list.Nil()))))), 
          Lit(#_module.list.Cons($Box(LitInt(3)), 
              Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil()))))))));
  ensures LitInt(_module.__default.size(TInt, 
        $LS($LS($LZ)), 
        Lit(_module.__default.app(TInt, 
            $LS($LS($LZ)), 
            Lit(#_module.list.Cons($Box(LitInt(1)), 
                Lit(#_module.list.Cons($Box(LitInt(2)), Lit(#_module.list.Nil()))))), 
            Lit(#_module.list.Cons($Box(LitInt(3)), 
                Lit(#_module.list.Cons($Box(LitInt(4)), Lit(#_module.list.Nil())))))))))
     == LitInt(4);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__appsize() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_appsize, Impl$$_module.__default.compute__appsize
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(78,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.interp
function _module.__default.interp($ly: LayerType, env#0: Map Box Box, e#0: DatatypeType) : int;

function _module.__default.interp#canCall(env#0: Map Box Box, e#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
  { _module.__default.interp($LS($ly), env#0, e#0) } 
  _module.__default.interp($LS($ly), env#0, e#0)
     == _module.__default.interp($ly, env#0, e#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
  { _module.__default.interp(AsFuelBottom($ly), env#0, e#0) } 
  _module.__default.interp($ly, env#0, e#0)
     == _module.__default.interp($LZ, env#0, e#0));

// consequence axiom for _module.__default.interp
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
    { _module.__default.interp($ly, env#0, e#0) } 
    _module.__default.interp#canCall(env#0, e#0)
         || (12 != $FunctionContextHeight
           && 
          $Is(env#0, TMap(TInt, TInt))
           && $Is(e#0, Tclass._module.exp()))
       ==> true);

function _module.__default.interp#requires(LayerType, Map Box Box, DatatypeType) : bool;

// #requires axiom for _module.__default.interp
axiom (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
  { _module.__default.interp#requires($ly, env#0, e#0) } 
  $Is(env#0, TMap(TInt, TInt)) && $Is(e#0, Tclass._module.exp())
     ==> _module.__default.interp#requires($ly, env#0, e#0) == true);

// definition axiom for _module.__default.interp (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
    { _module.__default.interp($LS($ly), env#0, e#0) } 
    _module.__default.interp#canCall(env#0, e#0)
         || (12 != $FunctionContextHeight
           && 
          $Is(env#0, TMap(TInt, TInt))
           && $Is(e#0, Tclass._module.exp()))
       ==> (_module.exp.Plus_q(e#0)
           ==> _module.__default.interp#canCall(env#0, _module.exp.e1(e#0))
             && _module.__default.interp#canCall(env#0, _module.exp.e2(e#0)))
         && _module.__default.interp($LS($ly), env#0, e#0)
           == (if _module.exp.Plus_q(e#0)
             then _module.__default.interp($ly, env#0, _module.exp.e1(e#0))
               + _module.__default.interp($ly, env#0, _module.exp.e2(e#0))
             else (if _module.exp.Num_q(e#0)
               then _module.exp.n(e#0)
               else (if _module.exp.Var_q(e#0) && Map#Domain(env#0)[$Box(_module.exp.x(e#0))]
                 then $Unbox(Map#Elements(env#0)[$Box(_module.exp.x(e#0))]): int
                 else 0))));

// definition axiom for _module.__default.interp for decreasing-related literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
    {:weight 3} { _module.__default.interp($LS($ly), env#0, Lit(e#0)) } 
    _module.__default.interp#canCall(env#0, Lit(e#0))
         || (12 != $FunctionContextHeight
           && 
          $Is(env#0, TMap(TInt, TInt))
           && $Is(e#0, Tclass._module.exp()))
       ==> (Lit(_module.exp.Plus_q(Lit(e#0)))
           ==> _module.__default.interp#canCall(env#0, Lit(_module.exp.e1(Lit(e#0))))
             && _module.__default.interp#canCall(env#0, Lit(_module.exp.e2(Lit(e#0)))))
         && _module.__default.interp($LS($ly), env#0, Lit(e#0))
           == (if _module.exp.Plus_q(Lit(e#0))
             then _module.__default.interp($LS($ly), env#0, Lit(_module.exp.e1(Lit(e#0))))
               + _module.__default.interp($LS($ly), env#0, Lit(_module.exp.e2(Lit(e#0))))
             else (if _module.exp.Num_q(Lit(e#0))
               then _module.exp.n(Lit(e#0))
               else (if _module.exp.Var_q(Lit(e#0)) && Map#Domain(env#0)[$Box(_module.exp.x(Lit(e#0)))]
                 then $Unbox(Map#Elements(env#0)[$Box(LitInt(_module.exp.x(Lit(e#0))))]): int
                 else 0))));

// definition axiom for _module.__default.interp for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
    {:weight 3} { _module.__default.interp($LS($ly), Lit(env#0), Lit(e#0)) } 
    _module.__default.interp#canCall(Lit(env#0), Lit(e#0))
         || (12 != $FunctionContextHeight
           && 
          $Is(env#0, TMap(TInt, TInt))
           && $Is(e#0, Tclass._module.exp()))
       ==> (Lit(_module.exp.Plus_q(Lit(e#0)))
           ==> _module.__default.interp#canCall(Lit(env#0), Lit(_module.exp.e1(Lit(e#0))))
             && _module.__default.interp#canCall(Lit(env#0), Lit(_module.exp.e2(Lit(e#0)))))
         && _module.__default.interp($LS($ly), Lit(env#0), Lit(e#0))
           == (if _module.exp.Plus_q(Lit(e#0))
             then _module.__default.interp($LS($ly), Lit(env#0), Lit(_module.exp.e1(Lit(e#0))))
               + _module.__default.interp($LS($ly), Lit(env#0), Lit(_module.exp.e2(Lit(e#0))))
             else (if _module.exp.Num_q(Lit(e#0))
               then _module.exp.n(Lit(e#0))
               else (if _module.exp.Var_q(Lit(e#0)) && Map#Domain(env#0)[$Box(_module.exp.x(Lit(e#0)))]
                 then $Unbox(Map#Elements(Lit(env#0))[$Box(LitInt(_module.exp.x(Lit(e#0))))]): int
                 else 0))));

procedure CheckWellformed$$_module.__default.interp(env#0: Map Box Box where $Is(env#0, TMap(TInt, TInt)), 
    e#0: DatatypeType where $Is(e#0, Tclass._module.exp()));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.interp(env#0: Map Box Box, e#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##env#0: Map Box Box;
  var ##e#0: DatatypeType;
  var ##env#1: Map Box Box;
  var ##e#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function interp
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(82,9): initial state"} true;
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
        if (_module.exp.Plus_q(e#0))
        {
            assert _module.exp.Plus_q(e#0);
            ##env#0 := env#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##env#0, TMap(TInt, TInt), $Heap);
            ##e#0 := _module.exp.e1(e#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#0, Tclass._module.exp(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##e#0) < DtRank(e#0);
            assume _module.__default.interp#canCall(env#0, _module.exp.e1(e#0));
            assert _module.exp.Plus_q(e#0);
            ##env#1 := env#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##env#1, TMap(TInt, TInt), $Heap);
            ##e#1 := _module.exp.e2(e#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#1, Tclass._module.exp(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##e#1) < DtRank(e#0);
            assume _module.__default.interp#canCall(env#0, _module.exp.e2(e#0));
            assume _module.__default.interp($LS($LZ), env#0, e#0)
               == _module.__default.interp($LS($LZ), env#0, _module.exp.e1(e#0))
                 + _module.__default.interp($LS($LZ), env#0, _module.exp.e2(e#0));
            assume _module.__default.interp#canCall(env#0, _module.exp.e1(e#0))
               && _module.__default.interp#canCall(env#0, _module.exp.e2(e#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.interp($LS($LZ), env#0, e#0), TInt);
        }
        else
        {
            if (_module.exp.Num_q(e#0))
            {
                assert _module.exp.Num_q(e#0);
                assume _module.__default.interp($LS($LZ), env#0, e#0) == _module.exp.n(e#0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.interp($LS($LZ), env#0, e#0), TInt);
            }
            else
            {
                if (_module.exp.Var_q(e#0))
                {
                    assert _module.exp.Var_q(e#0);
                }

                if (_module.exp.Var_q(e#0) && Map#Domain(env#0)[$Box(_module.exp.x(e#0))])
                {
                    assert _module.exp.Var_q(e#0);
                    assert Map#Domain(env#0)[$Box(_module.exp.x(e#0))];
                    assume _module.__default.interp($LS($LZ), env#0, e#0)
                       == $Unbox(Map#Elements(env#0)[$Box(_module.exp.x(e#0))]): int;
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.interp($LS($LZ), env#0, e#0), TInt);
                }
                else
                {
                    assume _module.__default.interp($LS($LZ), env#0, e#0) == LitInt(0);
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.interp($LS($LZ), env#0, e#0), TInt);
                }
            }
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.compute__interp1();
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__interp1();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.interp#canCall(Lit(Map#Empty(): Map Box Box), 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(1))), Lit(#_module.exp.Num(LitInt(2))))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(3))), Lit(#_module.exp.Num(LitInt(4))))))));
  ensures LitInt(_module.__default.interp($LS($LS($LZ)), 
        Lit(Map#Empty(): Map Box Box), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(1))), Lit(#_module.exp.Num(LitInt(2))))), 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(3))), Lit(#_module.exp.Num(LitInt(4)))))))))
     == LitInt(10);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__interp1() returns ($_reverifyPost: bool);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.interp#canCall(Lit(Map#Empty(): Map Box Box), 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(1))), Lit(#_module.exp.Num(LitInt(2))))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(3))), Lit(#_module.exp.Num(LitInt(4))))))));
  ensures LitInt(_module.__default.interp($LS($LS($LZ)), 
        Lit(Map#Empty(): Map Box Box), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(1))), Lit(#_module.exp.Num(LitInt(2))))), 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(3))), Lit(#_module.exp.Num(LitInt(4)))))))))
     == LitInt(10);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__interp1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_interp1, Impl$$_module.__default.compute__interp1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(92,0): initial state"} true;
    $_reverifyPost := false;
}



procedure {:_induction env#0} CheckWellformed$$_module.__default.compute__interp2(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap));
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction env#0} CheckWellformed$$_module.__default.compute__interp2(env#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##env#0: Map Box Box;
  var ##e#0: DatatypeType;

    // AddMethodImpl: compute_interp2, CheckWellformed$$_module.__default.compute__interp2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(94,13): initial state"} true;
    assume Map#Domain(env#0)[$Box(0)];
    assert Map#Domain(env#0)[$Box(LitInt(0))];
    assume $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(96,57): post-state"} true;
    ##env#0 := env#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##env#0, TMap(TInt, TInt), $Heap);
    ##e#0 := Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
        Lit(#_module.exp.Num(LitInt(0)))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass._module.exp(), $Heap);
    assume _module.__default.interp#canCall(env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
          Lit(#_module.exp.Num(LitInt(0))))));
    assume _module.__default.interp($LS($LZ), 
        env#0, 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
            Lit(#_module.exp.Num(LitInt(0))))))
       == LitInt(11);
}



procedure {:_induction env#0} Call$$_module.__default.compute__interp2(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap));
  // user-defined preconditions
  requires Map#Domain(env#0)[$Box(0)];
  requires $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.interp#canCall(env#0, 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
        Lit(#_module.exp.Num(LitInt(0))))));
  ensures _module.__default.interp($LS($LS($LZ)), 
      env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
          Lit(#_module.exp.Num(LitInt(0))))))
     == LitInt(11);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction env#0} Impl$$_module.__default.compute__interp2(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Domain(env#0)[$Box(0)];
  requires $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.interp#canCall(env#0, 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
        Lit(#_module.exp.Num(LitInt(0))))));
  ensures _module.__default.interp($LS($LS($LZ)), 
      env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
          Lit(#_module.exp.Num(LitInt(0))))))
     == LitInt(11);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction env#0} Impl$$_module.__default.compute__interp2(env#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: compute_interp2, Impl$$_module.__default.compute__interp2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(97,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#env0#0: Map Box Box :: 
      $Is($ih#env0#0, TMap(TInt, TInt))
           && 
          Map#Domain($ih#env0#0)[$Box(0)]
           && $Unbox(Map#Elements($ih#env0#0)[$Box(LitInt(0))]): int == LitInt(10)
           && 
          Set#Subset(Map#Domain($ih#env0#0), Map#Domain(env#0))
           && !Set#Subset(Map#Domain(env#0), Map#Domain($ih#env0#0))
         ==> _module.__default.interp($LS($LZ), 
            $ih#env0#0, 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
                Lit(#_module.exp.Num(LitInt(0))))))
           == LitInt(11));
    $_reverifyPost := false;
}



procedure {:_induction env#0} CheckWellformed$$_module.__default.compute__interp3(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap));
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction env#0} CheckWellformed$$_module.__default.compute__interp3(env#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##env#0: Map Box Box;
  var ##e#0: DatatypeType;

    // AddMethodImpl: compute_interp3, CheckWellformed$$_module.__default.compute__interp3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(99,13): initial state"} true;
    assume Map#Domain(env#0)[$Box(0)];
    assert Map#Domain(env#0)[$Box(LitInt(0))];
    assume $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
    assume !Map#Domain(env#0)[$Box(1)];
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(101,57): post-state"} true;
    ##env#0 := env#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##env#0, TMap(TInt, TInt), $Heap);
    ##e#0 := Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0)))))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass._module.exp(), $Heap);
    assume _module.__default.interp#canCall(env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))));
    assume _module.__default.interp($LS($LZ), 
        env#0, 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))))
       == LitInt(20);
}



procedure {:_induction env#0} Call$$_module.__default.compute__interp3(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap));
  // user-defined preconditions
  requires Map#Domain(env#0)[$Box(0)];
  requires $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
  requires !Map#Domain(env#0)[$Box(1)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.interp#canCall(env#0, 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))));
  ensures _module.__default.interp($LS($LS($LZ)), 
      env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))))
     == LitInt(20);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction env#0} Impl$$_module.__default.compute__interp3(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Domain(env#0)[$Box(0)];
  requires $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
  requires !Map#Domain(env#0)[$Box(1)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.interp#canCall(env#0, 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))));
  ensures _module.__default.interp($LS($LS($LZ)), 
      env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))))
     == LitInt(20);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction env#0} Impl$$_module.__default.compute__interp3(env#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: compute_interp3, Impl$$_module.__default.compute__interp3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(102,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#env0#0: Map Box Box :: 
      $Is($ih#env0#0, TMap(TInt, TInt))
           && 
          Map#Domain($ih#env0#0)[$Box(0)]
           && $Unbox(Map#Elements($ih#env0#0)[$Box(LitInt(0))]): int == LitInt(10)
           && !Map#Domain($ih#env0#0)[$Box(1)]
           && 
          Set#Subset(Map#Domain($ih#env0#0), Map#Domain(env#0))
           && !Set#Subset(Map#Domain(env#0), Map#Domain($ih#env0#0))
         ==> _module.__default.interp($LS($LZ), 
            $ih#env0#0, 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
                Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))))
           == LitInt(20));
    $_reverifyPost := false;
}



// function declaration for _module._default.cinterp
function _module.__default.cinterp($ly: LayerType, env#0: Map Box Box, e#0: DatatypeType) : int;

function _module.__default.cinterp#canCall(env#0: Map Box Box, e#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
  { _module.__default.cinterp($LS($ly), env#0, e#0) } 
  _module.__default.cinterp($LS($ly), env#0, e#0)
     == _module.__default.cinterp($ly, env#0, e#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
  { _module.__default.cinterp(AsFuelBottom($ly), env#0, e#0) } 
  _module.__default.cinterp($ly, env#0, e#0)
     == _module.__default.cinterp($LZ, env#0, e#0));

// consequence axiom for _module.__default.cinterp
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
    { _module.__default.cinterp($ly, env#0, e#0) } 
    _module.__default.cinterp#canCall(env#0, e#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(env#0, TMap(TInt, TInt))
           && $Is(e#0, Tclass._module.exp()))
       ==> true);

function _module.__default.cinterp#requires(LayerType, Map Box Box, DatatypeType) : bool;

// #requires axiom for _module.__default.cinterp
axiom (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
  { _module.__default.cinterp#requires($ly, env#0, e#0) } 
  $Is(env#0, TMap(TInt, TInt)) && $Is(e#0, Tclass._module.exp())
     ==> _module.__default.cinterp#requires($ly, env#0, e#0) == true);

// definition axiom for _module.__default.cinterp (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
    { _module.__default.cinterp($LS($ly), env#0, e#0) } 
    _module.__default.cinterp#canCall(env#0, e#0)
         || (13 != $FunctionContextHeight
           && 
          $Is(env#0, TMap(TInt, TInt))
           && $Is(e#0, Tclass._module.exp()))
       ==> (_module.exp.Plus_q(e#0)
           ==> (var e2#1 := _module.exp.e2(e#0); 
            (var e1#1 := _module.exp.e1(e#0); 
              _module.__default.cinterp#canCall(env#0, e1#1)
                 && _module.__default.cinterp#canCall(env#0, e2#1))))
         && _module.__default.cinterp($LS($ly), env#0, e#0)
           == (if _module.exp.Plus_q(e#0)
             then (var e2#0 := _module.exp.e2(e#0); 
              (var e1#0 := _module.exp.e1(e#0); 
                _module.__default.cinterp($ly, env#0, e1#0)
                   + _module.__default.cinterp($ly, env#0, e2#0)))
             else (if _module.exp.Num_q(e#0)
               then (var n#0 := _module.exp.n(e#0); n#0)
               else (var x#0 := _module.exp.x(e#0); 
                (if Map#Domain(env#0)[$Box(x#0)]
                   then $Unbox(Map#Elements(env#0)[$Box(x#0)]): int
                   else 0)))));

// definition axiom for _module.__default.cinterp for decreasing-related literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
    {:weight 3} { _module.__default.cinterp($LS($ly), env#0, Lit(e#0)) } 
    _module.__default.cinterp#canCall(env#0, Lit(e#0))
         || (13 != $FunctionContextHeight
           && 
          $Is(env#0, TMap(TInt, TInt))
           && $Is(e#0, Tclass._module.exp()))
       ==> (Lit(_module.exp.Plus_q(Lit(e#0)))
           ==> (var e2#3 := Lit(_module.exp.e2(Lit(e#0))); 
            (var e1#3 := Lit(_module.exp.e1(Lit(e#0))); 
              _module.__default.cinterp#canCall(env#0, e1#3)
                 && _module.__default.cinterp#canCall(env#0, e2#3))))
         && _module.__default.cinterp($LS($ly), env#0, Lit(e#0))
           == (if _module.exp.Plus_q(Lit(e#0))
             then (var e2#2 := Lit(_module.exp.e2(Lit(e#0))); 
              (var e1#2 := Lit(_module.exp.e1(Lit(e#0))); 
                _module.__default.cinterp($LS($ly), env#0, e1#2)
                   + _module.__default.cinterp($LS($ly), env#0, e2#2)))
             else (if _module.exp.Num_q(Lit(e#0))
               then (var n#2 := LitInt(_module.exp.n(Lit(e#0))); n#2)
               else (var x#2 := LitInt(_module.exp.x(Lit(e#0))); 
                (if Map#Domain(env#0)[$Box(x#2)]
                   then $Unbox(Map#Elements(env#0)[$Box(x#2)]): int
                   else 0)))));

// definition axiom for _module.__default.cinterp for all literals (revealed)
axiom 13 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, env#0: Map Box Box, e#0: DatatypeType :: 
    {:weight 3} { _module.__default.cinterp($LS($ly), Lit(env#0), Lit(e#0)) } 
    _module.__default.cinterp#canCall(Lit(env#0), Lit(e#0))
         || (13 != $FunctionContextHeight
           && 
          $Is(env#0, TMap(TInt, TInt))
           && $Is(e#0, Tclass._module.exp()))
       ==> (Lit(_module.exp.Plus_q(Lit(e#0)))
           ==> (var e2#5 := Lit(_module.exp.e2(Lit(e#0))); 
            (var e1#5 := Lit(_module.exp.e1(Lit(e#0))); 
              _module.__default.cinterp#canCall(Lit(env#0), e1#5)
                 && _module.__default.cinterp#canCall(Lit(env#0), e2#5))))
         && _module.__default.cinterp($LS($ly), Lit(env#0), Lit(e#0))
           == (if _module.exp.Plus_q(Lit(e#0))
             then (var e2#4 := Lit(_module.exp.e2(Lit(e#0))); 
              (var e1#4 := Lit(_module.exp.e1(Lit(e#0))); 
                LitInt(_module.__default.cinterp($LS($ly), Lit(env#0), e1#4)
                     + _module.__default.cinterp($LS($ly), Lit(env#0), e2#4))))
             else (if _module.exp.Num_q(Lit(e#0))
               then (var n#4 := LitInt(_module.exp.n(Lit(e#0))); n#4)
               else (var x#4 := LitInt(_module.exp.x(Lit(e#0))); 
                (if Map#Domain(env#0)[$Box(x#4)]
                   then $Unbox(Map#Elements(Lit(env#0))[$Box(x#4)]): int
                   else 0)))));

procedure CheckWellformed$$_module.__default.cinterp(env#0: Map Box Box where $Is(env#0, TMap(TInt, TInt)), 
    e#0: DatatypeType where $Is(e#0, Tclass._module.exp()));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.cinterp(env#0: Map Box Box, e#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#3#0: int;
  var x#Z#0: int;
  var let#0#0#0: int;
  var _mcc#2#0: int;
  var n#Z#0: int;
  var let#1#0#0: int;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var e2#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var e1#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var ##env#0: Map Box Box;
  var ##e#0: DatatypeType;
  var ##env#1: Map Box Box;
  var ##e#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function cinterp
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(104,9): initial state"} true;
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
        if (e#0 == #_module.exp.Plus(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.exp());
            assume $Is(_mcc#1#0, Tclass._module.exp());
            havoc e2#Z#0;
            assume $Is(e2#Z#0, Tclass._module.exp());
            assume let#2#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.exp());
            assume e2#Z#0 == let#2#0#0;
            havoc e1#Z#0;
            assume $Is(e1#Z#0, Tclass._module.exp());
            assume let#3#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, Tclass._module.exp());
            assume e1#Z#0 == let#3#0#0;
            ##env#0 := env#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##env#0, TMap(TInt, TInt), $Heap);
            ##e#0 := e1#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#0, Tclass._module.exp(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##e#0) < DtRank(e#0);
            assume _module.__default.cinterp#canCall(env#0, e1#Z#0);
            ##env#1 := env#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##env#1, TMap(TInt, TInt), $Heap);
            ##e#1 := e2#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#1, Tclass._module.exp(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##e#1) < DtRank(e#0);
            assume _module.__default.cinterp#canCall(env#0, e2#Z#0);
            assume _module.__default.cinterp($LS($LZ), env#0, e#0)
               == _module.__default.cinterp($LS($LZ), env#0, e1#Z#0)
                 + _module.__default.cinterp($LS($LZ), env#0, e2#Z#0);
            assume _module.__default.cinterp#canCall(env#0, e1#Z#0)
               && _module.__default.cinterp#canCall(env#0, e2#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.cinterp($LS($LZ), env#0, e#0), TInt);
        }
        else if (e#0 == #_module.exp.Num(_mcc#2#0))
        {
            havoc n#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume n#Z#0 == let#1#0#0;
            assume _module.__default.cinterp($LS($LZ), env#0, e#0) == n#Z#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.cinterp($LS($LZ), env#0, e#0), TInt);
        }
        else if (e#0 == #_module.exp.Var(_mcc#3#0))
        {
            havoc x#Z#0;
            assume true;
            assume let#0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, TInt);
            assume x#Z#0 == let#0#0#0;
            if (Map#Domain(env#0)[$Box(x#Z#0)])
            {
                assert Map#Domain(env#0)[$Box(x#Z#0)];
                assume _module.__default.cinterp($LS($LZ), env#0, e#0)
                   == $Unbox(Map#Elements(env#0)[$Box(x#Z#0)]): int;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.cinterp($LS($LZ), env#0, e#0), TInt);
            }
            else
            {
                assume _module.__default.cinterp($LS($LZ), env#0, e#0) == LitInt(0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.cinterp($LS($LZ), env#0, e#0), TInt);
            }
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.compute__cinterp1();
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.compute__cinterp1();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cinterp#canCall(Lit(Map#Empty(): Map Box Box), 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(1))), Lit(#_module.exp.Num(LitInt(2))))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(3))), Lit(#_module.exp.Num(LitInt(4))))))));
  ensures LitInt(_module.__default.cinterp($LS($LS($LZ)), 
        Lit(Map#Empty(): Map Box Box), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(1))), Lit(#_module.exp.Num(LitInt(2))))), 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(3))), Lit(#_module.exp.Num(LitInt(4)))))))))
     == LitInt(10);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.compute__cinterp1() returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cinterp#canCall(Lit(Map#Empty(): Map Box Box), 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(1))), Lit(#_module.exp.Num(LitInt(2))))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(3))), Lit(#_module.exp.Num(LitInt(4))))))));
  ensures LitInt(_module.__default.cinterp($LS($LS($LZ)), 
        Lit(Map#Empty(): Map Box Box), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(1))), Lit(#_module.exp.Num(LitInt(2))))), 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(3))), Lit(#_module.exp.Num(LitInt(4)))))))))
     == LitInt(10);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.compute__cinterp1() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: compute_cinterp1, Impl$$_module.__default.compute__cinterp1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(114,0): initial state"} true;
    $_reverifyPost := false;
}



procedure {:_induction env#0} CheckWellformed$$_module.__default.compute__cinterp2(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction env#0} CheckWellformed$$_module.__default.compute__cinterp2(env#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##env#0: Map Box Box;
  var ##e#0: DatatypeType;

    // AddMethodImpl: compute_cinterp2, CheckWellformed$$_module.__default.compute__cinterp2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(116,13): initial state"} true;
    assume Map#Domain(env#0)[$Box(0)];
    assert Map#Domain(env#0)[$Box(LitInt(0))];
    assume $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(118,58): post-state"} true;
    ##env#0 := env#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##env#0, TMap(TInt, TInt), $Heap);
    ##e#0 := Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
        Lit(#_module.exp.Num(LitInt(0)))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass._module.exp(), $Heap);
    assume _module.__default.cinterp#canCall(env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
          Lit(#_module.exp.Num(LitInt(0))))));
    assume _module.__default.cinterp($LS($LZ), 
        env#0, 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
            Lit(#_module.exp.Num(LitInt(0))))))
       == LitInt(11);
}



procedure {:_induction env#0} Call$$_module.__default.compute__cinterp2(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap));
  // user-defined preconditions
  requires Map#Domain(env#0)[$Box(0)];
  requires $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cinterp#canCall(env#0, 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
        Lit(#_module.exp.Num(LitInt(0))))));
  ensures _module.__default.cinterp($LS($LS($LZ)), 
      env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
          Lit(#_module.exp.Num(LitInt(0))))))
     == LitInt(11);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction env#0} Impl$$_module.__default.compute__cinterp2(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Domain(env#0)[$Box(0)];
  requires $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cinterp#canCall(env#0, 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
        Lit(#_module.exp.Num(LitInt(0))))));
  ensures _module.__default.cinterp($LS($LS($LZ)), 
      env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
          Lit(#_module.exp.Num(LitInt(0))))))
     == LitInt(11);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction env#0} Impl$$_module.__default.compute__cinterp2(env#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: compute_cinterp2, Impl$$_module.__default.compute__cinterp2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(119,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#env0#0: Map Box Box :: 
      $Is($ih#env0#0, TMap(TInt, TInt))
           && 
          Map#Domain($ih#env0#0)[$Box(0)]
           && $Unbox(Map#Elements($ih#env0#0)[$Box(LitInt(0))]): int == LitInt(10)
           && 
          Set#Subset(Map#Domain($ih#env0#0), Map#Domain(env#0))
           && !Set#Subset(Map#Domain(env#0), Map#Domain($ih#env0#0))
         ==> _module.__default.cinterp($LS($LZ), 
            $ih#env0#0, 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), Lit(#_module.exp.Num(LitInt(1))))), 
                Lit(#_module.exp.Num(LitInt(0))))))
           == LitInt(11));
    $_reverifyPost := false;
}



procedure {:_induction env#0} CheckWellformed$$_module.__default.compute__cinterp3(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap));
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction env#0} CheckWellformed$$_module.__default.compute__cinterp3(env#0: Map Box Box)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##env#0: Map Box Box;
  var ##e#0: DatatypeType;

    // AddMethodImpl: compute_cinterp3, CheckWellformed$$_module.__default.compute__cinterp3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(121,13): initial state"} true;
    assume Map#Domain(env#0)[$Box(0)];
    assert Map#Domain(env#0)[$Box(LitInt(0))];
    assume $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
    assume !Map#Domain(env#0)[$Box(1)];
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(123,58): post-state"} true;
    ##env#0 := env#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##env#0, TMap(TInt, TInt), $Heap);
    ##e#0 := Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0)))))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##e#0, Tclass._module.exp(), $Heap);
    assume _module.__default.cinterp#canCall(env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))));
    assume _module.__default.cinterp($LS($LZ), 
        env#0, 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))))
       == LitInt(20);
}



procedure {:_induction env#0} Call$$_module.__default.compute__cinterp3(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap));
  // user-defined preconditions
  requires Map#Domain(env#0)[$Box(0)];
  requires $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
  requires !Map#Domain(env#0)[$Box(1)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cinterp#canCall(env#0, 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))));
  ensures _module.__default.cinterp($LS($LS($LZ)), 
      env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))))
     == LitInt(20);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction env#0} Impl$$_module.__default.compute__cinterp3(env#0: Map Box Box
       where $Is(env#0, TMap(TInt, TInt)) && $IsAlloc(env#0, TMap(TInt, TInt), $Heap))
   returns ($_reverifyPost: bool);
  free requires 35 == $FunctionContextHeight;
  // user-defined preconditions
  requires Map#Domain(env#0)[$Box(0)];
  requires $Unbox(Map#Elements(env#0)[$Box(LitInt(0))]): int == LitInt(10);
  requires !Map#Domain(env#0)[$Box(1)];
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.cinterp#canCall(env#0, 
    Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
        Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))));
  ensures _module.__default.cinterp($LS($LS($LZ)), 
      env#0, 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))))
     == LitInt(20);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction env#0} Impl$$_module.__default.compute__cinterp3(env#0: Map Box Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: compute_cinterp3, Impl$$_module.__default.compute__cinterp3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(124,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#env0#0: Map Box Box :: 
      $Is($ih#env0#0, TMap(TInt, TInt))
           && 
          Map#Domain($ih#env0#0)[$Box(0)]
           && $Unbox(Map#Elements($ih#env0#0)[$Box(LitInt(0))]): int == LitInt(10)
           && !Map#Domain($ih#env0#0)[$Box(1)]
           && 
          Set#Subset(Map#Domain($ih#env0#0), Map#Domain(env#0))
           && !Set#Subset(Map#Domain(env#0), Map#Domain($ih#env0#0))
         ==> _module.__default.cinterp($LS($LZ), 
            $ih#env0#0, 
            Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(0))), 
                Lit(#_module.exp.Plus(Lit(#_module.exp.Var(LitInt(1))), Lit(#_module.exp.Var(LitInt(0))))))))
           == LitInt(20));
    $_reverifyPost := false;
}



// function declaration for _module._default.opt
function _module.__default.opt($ly: LayerType, e#0: DatatypeType) : DatatypeType;

function _module.__default.opt#canCall(e#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, e#0: DatatypeType :: 
  { _module.__default.opt($LS($ly), e#0) } 
  _module.__default.opt($LS($ly), e#0) == _module.__default.opt($ly, e#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, e#0: DatatypeType :: 
  { _module.__default.opt(AsFuelBottom($ly), e#0) } 
  _module.__default.opt($ly, e#0) == _module.__default.opt($LZ, e#0));

// consequence axiom for _module.__default.opt
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType :: 
    { _module.__default.opt($ly, e#0) } 
    _module.__default.opt#canCall(e#0)
         || (14 != $FunctionContextHeight && $Is(e#0, Tclass._module.exp()))
       ==> $Is(_module.__default.opt($ly, e#0), Tclass._module.exp()));

function _module.__default.opt#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.opt
axiom (forall $ly: LayerType, e#0: DatatypeType :: 
  { _module.__default.opt#requires($ly, e#0) } 
  $Is(e#0, Tclass._module.exp())
     ==> _module.__default.opt#requires($ly, e#0) == true);

// definition axiom for _module.__default.opt (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType :: 
    { _module.__default.opt($LS($ly), e#0) } 
    _module.__default.opt#canCall(e#0)
         || (14 != $FunctionContextHeight && $Is(e#0, Tclass._module.exp()))
       ==> (_module.exp.Plus_q(e#0)
           ==> (var e1#1 := _module.exp.e1(e#0); _module.__default.opt#canCall(e1#1)))
         && _module.__default.opt($LS($ly), e#0)
           == (if _module.exp.Plus_q(e#0)
             then (var e2#0 := _module.exp.e2(e#0); 
              (var e1#0 := _module.exp.e1(e#0); 
                (var o1#0 := _module.__default.opt($ly, e1#0); 
                  (if _module.exp.Num_q(o1#0) && _module.exp.n(o1#0) == LitInt(0)
                     then e2#0
                     else #_module.exp.Plus(o1#0, e2#0)))))
             else (if _module.exp.Num_q(e#0)
               then (var n#0 := _module.exp.n(e#0); e#0)
               else (var x#0 := _module.exp.x(e#0); e#0))));

// definition axiom for _module.__default.opt for all literals (revealed)
axiom 14 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType :: 
    {:weight 3} { _module.__default.opt($LS($ly), Lit(e#0)) } 
    _module.__default.opt#canCall(Lit(e#0))
         || (14 != $FunctionContextHeight && $Is(e#0, Tclass._module.exp()))
       ==> (Lit(_module.exp.Plus_q(Lit(e#0)))
           ==> (var e1#3 := Lit(_module.exp.e1(Lit(e#0))); _module.__default.opt#canCall(e1#3)))
         && _module.__default.opt($LS($ly), Lit(e#0))
           == (if _module.exp.Plus_q(Lit(e#0))
             then (var e2#2 := Lit(_module.exp.e2(Lit(e#0))); 
              (var e1#2 := Lit(_module.exp.e1(Lit(e#0))); 
                (var o1#2 := Lit(_module.__default.opt($LS($ly), e1#2)); 
                  (if _module.exp.Num_q(o1#2) && LitInt(_module.exp.n(o1#2)) == LitInt(0)
                     then e2#2
                     else #_module.exp.Plus(o1#2, e2#2)))))
             else (if _module.exp.Num_q(Lit(e#0))
               then (var n#2 := LitInt(_module.exp.n(Lit(e#0))); Lit(e#0))
               else (var x#2 := LitInt(_module.exp.x(Lit(e#0))); Lit(e#0)))));

procedure CheckWellformed$$_module.__default.opt(e#0: DatatypeType where $Is(e#0, Tclass._module.exp()));
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.opt(e#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#3#0: int;
  var x#Z#0: int;
  var let#0#0#0: int;
  var _mcc#2#0: int;
  var n#Z#0: int;
  var let#1#0#0: int;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var e2#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var e1#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var o1#Z#0: DatatypeType;
  var let#4#0#0: DatatypeType;
  var ##e#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function opt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(127,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.opt($LS($LZ), e#0), Tclass._module.exp());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (e#0 == #_module.exp.Plus(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.exp());
            assume $Is(_mcc#1#0, Tclass._module.exp());
            havoc e2#Z#0;
            assume $Is(e2#Z#0, Tclass._module.exp());
            assume let#2#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.exp());
            assume e2#Z#0 == let#2#0#0;
            havoc e1#Z#0;
            assume $Is(e1#Z#0, Tclass._module.exp());
            assume let#3#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, Tclass._module.exp());
            assume e1#Z#0 == let#3#0#0;
            havoc o1#Z#0;
            assume $Is(o1#Z#0, Tclass._module.exp());
            ##e#0 := e1#Z#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##e#0, Tclass._module.exp(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert DtRank(##e#0) < DtRank(e#0);
            assume _module.__default.opt#canCall(e1#Z#0);
            assume let#4#0#0 == _module.__default.opt($LS($LZ), e1#Z#0);
            assume _module.__default.opt#canCall(e1#Z#0);
            // CheckWellformedWithResult: any expression
            assume $Is(let#4#0#0, Tclass._module.exp());
            assume o1#Z#0 == let#4#0#0;
            if (_module.exp.Num_q(o1#Z#0))
            {
                assert _module.exp.Num_q(o1#Z#0);
            }

            if (_module.exp.Num_q(o1#Z#0) && _module.exp.n(o1#Z#0) == LitInt(0))
            {
                assume _module.__default.opt($LS($LZ), e#0) == e2#Z#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.opt($LS($LZ), e#0), Tclass._module.exp());
            }
            else
            {
                assume _module.__default.opt($LS($LZ), e#0) == #_module.exp.Plus(o1#Z#0, e2#Z#0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.opt($LS($LZ), e#0), Tclass._module.exp());
            }
        }
        else if (e#0 == #_module.exp.Num(_mcc#2#0))
        {
            havoc n#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume n#Z#0 == let#1#0#0;
            assume _module.__default.opt($LS($LZ), e#0) == e#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.opt($LS($LZ), e#0), Tclass._module.exp());
        }
        else if (e#0 == #_module.exp.Var(_mcc#3#0))
        {
            havoc x#Z#0;
            assume true;
            assume let#0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, TInt);
            assume x#Z#0 == let#0#0#0;
            assume _module.__default.opt($LS($LZ), e#0) == e#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.opt($LS($LZ), e#0), Tclass._module.exp());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.opt__test();
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.opt__test();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.exp(Lit(_module.__default.opt($LS($LZ), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
                  Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(1))))))))
     && _module.__default.opt#canCall(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(0))))), 
          Lit(#_module.exp.Num(LitInt(1))))));
  ensures _module.exp#Equal(_module.__default.opt($LS($LS($LZ)), 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(0))))), 
          Lit(#_module.exp.Num(LitInt(1)))))), 
    #_module.exp.Num(LitInt(1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.opt__test() returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.exp(Lit(_module.__default.opt($LS($LZ), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
                  Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(1))))))))
     && _module.__default.opt#canCall(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(0))))), 
          Lit(#_module.exp.Num(LitInt(1))))));
  ensures _module.exp#Equal(_module.__default.opt($LS($LS($LZ)), 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(0))))), 
          Lit(#_module.exp.Num(LitInt(1)))))), 
    #_module.exp.Num(LitInt(1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.opt__test() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: opt_test, Impl$$_module.__default.opt__test
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(138,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.copt
function _module.__default.copt($ly: LayerType, e#0: DatatypeType) : DatatypeType;

function _module.__default.copt#canCall(e#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, e#0: DatatypeType :: 
  { _module.__default.copt($LS($ly), e#0) } 
  _module.__default.copt($LS($ly), e#0) == _module.__default.copt($ly, e#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, e#0: DatatypeType :: 
  { _module.__default.copt(AsFuelBottom($ly), e#0) } 
  _module.__default.copt($ly, e#0) == _module.__default.copt($LZ, e#0));

// consequence axiom for _module.__default.copt
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType :: 
    { _module.__default.copt($ly, e#0) } 
    _module.__default.copt#canCall(e#0)
         || (15 != $FunctionContextHeight && $Is(e#0, Tclass._module.exp()))
       ==> $Is(_module.__default.copt($ly, e#0), Tclass._module.exp()));

function _module.__default.copt#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.copt
axiom (forall $ly: LayerType, e#0: DatatypeType :: 
  { _module.__default.copt#requires($ly, e#0) } 
  $Is(e#0, Tclass._module.exp())
     ==> _module.__default.copt#requires($ly, e#0) == true);

// definition axiom for _module.__default.copt (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType :: 
    { _module.__default.copt($LS($ly), e#0) } 
    _module.__default.copt#canCall(e#0)
         || (15 != $FunctionContextHeight && $Is(e#0, Tclass._module.exp()))
       ==> (_module.exp.Plus_q(e#0)
           ==> (var e1#1 := _module.exp.e1(e#0); 
            _module.exp.Plus_q(e1#1) ==> _module.__default.copt#canCall(e1#1)))
         && _module.__default.copt($LS($ly), e#0)
           == (if _module.exp.Plus_q(e#0)
             then (var e2#0 := _module.exp.e2(e#0); 
              (var e1#0 := _module.exp.e1(e#0); 
                (if _module.exp.Plus_q(e1#0)
                   then (var e12#0 := _module.exp.e2(e1#0); 
                    (var e11#0 := _module.exp.e1(e1#0); 
                      (var o1#0 := _module.__default.copt($ly, e1#0); 
                        (if _module.exp.Num_q(o1#0) && _module.exp.n(o1#0) == LitInt(0)
                           then e2#0
                           else #_module.exp.Plus(o1#0, e2#0)))))
                   else (if _module.exp.Num_q(e1#0)
                     then (var n#0 := _module.exp.n(e1#0); (if n#0 == LitInt(0) then e2#0 else e#0))
                     else (var x#0 := _module.exp.x(e1#0); e#0)))))
             else (if _module.exp.Num_q(e#0)
               then (var n#1 := _module.exp.n(e#0); e#0)
               else (var x#1 := _module.exp.x(e#0); e#0))));

// definition axiom for _module.__default.copt for all literals (revealed)
axiom 15 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, e#0: DatatypeType :: 
    {:weight 3} { _module.__default.copt($LS($ly), Lit(e#0)) } 
    _module.__default.copt#canCall(Lit(e#0))
         || (15 != $FunctionContextHeight && $Is(e#0, Tclass._module.exp()))
       ==> (Lit(_module.exp.Plus_q(Lit(e#0)))
           ==> (var e1#3 := Lit(_module.exp.e1(Lit(e#0))); 
            _module.exp.Plus_q(e1#3) ==> _module.__default.copt#canCall(e1#3)))
         && _module.__default.copt($LS($ly), Lit(e#0))
           == (if _module.exp.Plus_q(Lit(e#0))
             then (var e2#2 := Lit(_module.exp.e2(Lit(e#0))); 
              (var e1#2 := Lit(_module.exp.e1(Lit(e#0))); 
                (if _module.exp.Plus_q(e1#2)
                   then (var e12#2 := Lit(_module.exp.e2(e1#2)); 
                    (var e11#2 := Lit(_module.exp.e1(e1#2)); 
                      (var o1#2 := Lit(_module.__default.copt($LS($ly), e1#2)); 
                        (if _module.exp.Num_q(o1#2) && LitInt(_module.exp.n(o1#2)) == LitInt(0)
                           then e2#2
                           else #_module.exp.Plus(o1#2, e2#2)))))
                   else (if _module.exp.Num_q(e1#2)
                     then (var n#4 := LitInt(_module.exp.n(e1#2)); 
                      (if n#4 == LitInt(0) then e2#2 else e#0))
                     else (var x#4 := LitInt(_module.exp.x(e1#2)); Lit(e#0))))))
             else (if _module.exp.Num_q(Lit(e#0))
               then (var n#5 := LitInt(_module.exp.n(Lit(e#0))); Lit(e#0))
               else (var x#5 := LitInt(_module.exp.x(Lit(e#0))); Lit(e#0)))));

procedure CheckWellformed$$_module.__default.copt(e#0: DatatypeType where $Is(e#0, Tclass._module.exp()));
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.copt(e#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#3#0: int;
  var x#Z#0: int;
  var let#0#0#0: int;
  var _mcc#2#0: int;
  var n#Z#0: int;
  var let#1#0#0: int;
  var _mcc#0#0: DatatypeType;
  var _mcc#1#0: DatatypeType;
  var e2#Z#0: DatatypeType;
  var let#2#0#0: DatatypeType;
  var e1#Z#0: DatatypeType;
  var let#3#0#0: DatatypeType;
  var _mcc#7#0: int;
  var x#Z#1: int;
  var let#4#0#0: int;
  var _mcc#6#0: int;
  var n#Z#1: int;
  var let#5#0#0: int;
  var _mcc#4#0: DatatypeType;
  var _mcc#5#0: DatatypeType;
  var e12#Z#0: DatatypeType;
  var let#6#0#0: DatatypeType;
  var e11#Z#0: DatatypeType;
  var let#7#0#0: DatatypeType;
  var o1#Z#0: DatatypeType;
  var let#8#0#0: DatatypeType;
  var ##e#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function copt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(140,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.copt($LS($LZ), e#0), Tclass._module.exp());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (e#0 == #_module.exp.Plus(_mcc#0#0, _mcc#1#0))
        {
            assume $Is(_mcc#0#0, Tclass._module.exp());
            assume $Is(_mcc#1#0, Tclass._module.exp());
            havoc e2#Z#0;
            assume $Is(e2#Z#0, Tclass._module.exp());
            assume let#2#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, Tclass._module.exp());
            assume e2#Z#0 == let#2#0#0;
            havoc e1#Z#0;
            assume $Is(e1#Z#0, Tclass._module.exp());
            assume let#3#0#0 == _mcc#0#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#3#0#0, Tclass._module.exp());
            assume e1#Z#0 == let#3#0#0;
            if (e1#Z#0 == #_module.exp.Plus(_mcc#4#0, _mcc#5#0))
            {
                assume $Is(_mcc#4#0, Tclass._module.exp());
                assume $Is(_mcc#5#0, Tclass._module.exp());
                havoc e12#Z#0;
                assume $Is(e12#Z#0, Tclass._module.exp());
                assume let#6#0#0 == _mcc#5#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#6#0#0, Tclass._module.exp());
                assume e12#Z#0 == let#6#0#0;
                havoc e11#Z#0;
                assume $Is(e11#Z#0, Tclass._module.exp());
                assume let#7#0#0 == _mcc#4#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#7#0#0, Tclass._module.exp());
                assume e11#Z#0 == let#7#0#0;
                havoc o1#Z#0;
                assume $Is(o1#Z#0, Tclass._module.exp());
                ##e#0 := e1#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##e#0, Tclass._module.exp(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##e#0) < DtRank(e#0);
                assume _module.__default.copt#canCall(e1#Z#0);
                assume let#8#0#0 == _module.__default.copt($LS($LZ), e1#Z#0);
                assume _module.__default.copt#canCall(e1#Z#0);
                // CheckWellformedWithResult: any expression
                assume $Is(let#8#0#0, Tclass._module.exp());
                assume o1#Z#0 == let#8#0#0;
                if (_module.exp.Num_q(o1#Z#0))
                {
                    assert _module.exp.Num_q(o1#Z#0);
                }

                if (_module.exp.Num_q(o1#Z#0) && _module.exp.n(o1#Z#0) == LitInt(0))
                {
                    assume _module.__default.copt($LS($LZ), e#0) == e2#Z#0;
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.copt($LS($LZ), e#0), Tclass._module.exp());
                }
                else
                {
                    assume _module.__default.copt($LS($LZ), e#0) == #_module.exp.Plus(o1#Z#0, e2#Z#0);
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.copt($LS($LZ), e#0), Tclass._module.exp());
                }
            }
            else if (e1#Z#0 == #_module.exp.Num(_mcc#6#0))
            {
                havoc n#Z#1;
                assume true;
                assume let#5#0#0 == _mcc#6#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#5#0#0, TInt);
                assume n#Z#1 == let#5#0#0;
                if (n#Z#1 == LitInt(0))
                {
                    assume _module.__default.copt($LS($LZ), e#0) == e2#Z#0;
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.copt($LS($LZ), e#0), Tclass._module.exp());
                }
                else
                {
                    assume _module.__default.copt($LS($LZ), e#0) == e#0;
                    assume true;
                    // CheckWellformedWithResult: any expression
                    assume $Is(_module.__default.copt($LS($LZ), e#0), Tclass._module.exp());
                }
            }
            else if (e1#Z#0 == #_module.exp.Var(_mcc#7#0))
            {
                havoc x#Z#1;
                assume true;
                assume let#4#0#0 == _mcc#7#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(let#4#0#0, TInt);
                assume x#Z#1 == let#4#0#0;
                assume _module.__default.copt($LS($LZ), e#0) == e#0;
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(_module.__default.copt($LS($LZ), e#0), Tclass._module.exp());
            }
            else
            {
                assume false;
            }
        }
        else if (e#0 == #_module.exp.Num(_mcc#2#0))
        {
            havoc n#Z#0;
            assume true;
            assume let#1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, TInt);
            assume n#Z#0 == let#1#0#0;
            assume _module.__default.copt($LS($LZ), e#0) == e#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.copt($LS($LZ), e#0), Tclass._module.exp());
        }
        else if (e#0 == #_module.exp.Var(_mcc#3#0))
        {
            havoc x#Z#0;
            assume true;
            assume let#0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, TInt);
            assume x#Z#0 == let#0#0#0;
            assume _module.__default.copt($LS($LZ), e#0) == e#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.copt($LS($LZ), e#0), Tclass._module.exp());
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.copt__test();
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.copt__test();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.exp(Lit(_module.__default.copt($LS($LZ), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
                  Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(1))))))))
     && _module.__default.copt#canCall(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(0))))), 
          Lit(#_module.exp.Num(LitInt(1))))));
  ensures _module.exp#Equal(_module.__default.copt($LS($LS($LZ)), 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(0))))), 
          Lit(#_module.exp.Num(LitInt(1)))))), 
    #_module.exp.Num(LitInt(1)));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.copt__test() returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.exp(Lit(_module.__default.copt($LS($LZ), 
          Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
                  Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(1))))))))
     && _module.__default.copt#canCall(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(0))))), 
          Lit(#_module.exp.Num(LitInt(1))))));
  ensures _module.exp#Equal(_module.__default.copt($LS($LS($LZ)), 
      Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Plus(Lit(#_module.exp.Num(LitInt(0))), Lit(#_module.exp.Num(LitInt(0))))), 
              Lit(#_module.exp.Num(LitInt(0))))), 
          Lit(#_module.exp.Num(LitInt(1)))))), 
    #_module.exp.Num(LitInt(1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.copt__test() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: copt_test, Impl$$_module.__default.copt__test
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(154,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.power
function _module.__default.power($ly: LayerType, b#0: int, n#0: int) : int;

function _module.__default.power#canCall(b#0: int, n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, b#0: int, n#0: int :: 
  { _module.__default.power($LS($ly), b#0, n#0) } 
  _module.__default.power($LS($ly), b#0, n#0)
     == _module.__default.power($ly, b#0, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, b#0: int, n#0: int :: 
  { _module.__default.power(AsFuelBottom($ly), b#0, n#0) } 
  _module.__default.power($ly, b#0, n#0) == _module.__default.power($LZ, b#0, n#0));

// consequence axiom for _module.__default.power
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: int, n#0: int :: 
    { _module.__default.power($ly, b#0, n#0) } 
    _module.__default.power#canCall(b#0, n#0)
         || (16 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> true);

function _module.__default.power#requires(LayerType, int, int) : bool;

// #requires axiom for _module.__default.power
axiom (forall $ly: LayerType, b#0: int, n#0: int :: 
  { _module.__default.power#requires($ly, b#0, n#0) } 
  LitInt(0) <= n#0 ==> _module.__default.power#requires($ly, b#0, n#0) == true);

// definition axiom for _module.__default.power (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: int, n#0: int :: 
    { _module.__default.power($LS($ly), b#0, n#0) } 
    _module.__default.power#canCall(b#0, n#0)
         || (16 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (n#0 != LitInt(0) ==> _module.__default.power#canCall(b#0, n#0 - 1))
         && _module.__default.power($LS($ly), b#0, n#0)
           == (if n#0 == LitInt(0)
             then 1
             else Mul(b#0, _module.__default.power($ly, b#0, n#0 - 1))));

// definition axiom for _module.__default.power for all literals (revealed)
axiom 16 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, b#0: int, n#0: int :: 
    {:weight 3} { _module.__default.power($LS($ly), LitInt(b#0), LitInt(n#0)) } 
    _module.__default.power#canCall(LitInt(b#0), LitInt(n#0))
         || (16 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.__default.power#canCall(LitInt(b#0), LitInt(n#0 - 1)))
         && _module.__default.power($LS($ly), LitInt(b#0), LitInt(n#0))
           == (if LitInt(n#0) == LitInt(0)
             then 1
             else Mul(LitInt(b#0), 
              LitInt(_module.__default.power($LS($ly), LitInt(b#0), LitInt(n#0 - 1))))));

procedure CheckWellformed$$_module.__default.power(b#0: int, n#0: int where LitInt(0) <= n#0);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.power(b#0: int, n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b#0: int;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function power
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(157,9): initial state"} true;
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
        if (n#0 == LitInt(0))
        {
            assume _module.__default.power($LS($LZ), b#0, n#0) == LitInt(1);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.power($LS($LZ), b#0, n#0), TInt);
        }
        else
        {
            ##b#0 := b#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#0, TInt, $Heap);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= b#0 || ##b#0 == b#0;
            assert 0 <= n#0 || ##b#0 < b#0 || ##n#0 == n#0;
            assert ##b#0 < b#0 || (##b#0 == b#0 && ##n#0 < n#0);
            assume _module.__default.power#canCall(b#0, n#0 - 1);
            assume _module.__default.power($LS($LZ), b#0, n#0)
               == Mul(b#0, _module.__default.power($LS($LZ), b#0, n#0 - 1));
            assume _module.__default.power#canCall(b#0, n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.power($LS($LZ), b#0, n#0), TInt);
        }

        assert b$reqreads#0;
    }
}



procedure CheckWellformed$$_module.__default.test__power();
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.test__power()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##b#0: int;
  var ##n#0: int;
  var ##b#1: int;
  var ##n#1: int;
  var ##b#2: int;
  var ##n#2: int;

    // AddMethodImpl: test_power, CheckWellformed$$_module.__default.test__power
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(161,13): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(162,43): post-state"} true;
    ##b#0 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, TInt, $Heap);
    assert $Is(LitInt(3), Tclass._System.nat());
    ##n#0 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.power#canCall(LitInt(2), LitInt(3));
    ##b#1 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, TInt, $Heap);
    assert $Is(LitInt(2), Tclass._System.nat());
    ##n#1 := LitInt(2);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    assume _module.__default.power#canCall(LitInt(2), LitInt(2));
    ##b#2 := LitInt(_module.__default.power($LS($LZ), LitInt(2), LitInt(3)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#2, TInt, $Heap);
    assert $Is(LitInt(1 + _module.__default.power($LS($LZ), LitInt(2), LitInt(2))), 
      Tclass._System.nat());
    ##n#2 := LitInt(1 + _module.__default.power($LS($LZ), LitInt(2), LitInt(2)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
    assume _module.__default.power#canCall(LitInt(_module.__default.power($LS($LZ), LitInt(2), LitInt(3))), 
      LitInt(1 + _module.__default.power($LS($LZ), LitInt(2), LitInt(2))));
    assume LitInt(_module.__default.power($LS($LZ), 
          LitInt(_module.__default.power($LS($LZ), LitInt(2), LitInt(3))), 
          LitInt(1 + _module.__default.power($LS($LZ), LitInt(2), LitInt(2)))))
       == LitInt(32768);
}



procedure Call$$_module.__default.test__power();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.power#canCall(LitInt(2), LitInt(3))
     && _module.__default.power#canCall(LitInt(2), LitInt(2))
     && _module.__default.power#canCall(LitInt(_module.__default.power($LS($LZ), LitInt(2), LitInt(3))), 
      LitInt(1 + _module.__default.power($LS($LZ), LitInt(2), LitInt(2))));
  ensures LitInt(_module.__default.power($LS($LS($LZ)), 
        LitInt(_module.__default.power($LS($LS($LZ)), LitInt(2), LitInt(3))), 
        LitInt(1 + _module.__default.power($LS($LS($LZ)), LitInt(2), LitInt(2)))))
     == LitInt(32768);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.test__power() returns ($_reverifyPost: bool);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.power#canCall(LitInt(2), LitInt(3))
     && _module.__default.power#canCall(LitInt(2), LitInt(2))
     && _module.__default.power#canCall(LitInt(_module.__default.power($LS($LZ), LitInt(2), LitInt(3))), 
      LitInt(1 + _module.__default.power($LS($LZ), LitInt(2), LitInt(2))));
  ensures LitInt(_module.__default.power($LS($LS($LZ)), 
        LitInt(_module.__default.power($LS($LS($LZ)), LitInt(2), LitInt(3))), 
        LitInt(1 + _module.__default.power($LS($LS($LZ)), LitInt(2), LitInt(2)))))
     == LitInt(32768);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.test__power() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: test_power, Impl$$_module.__default.test__power
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(163,0): initial state"} true;
    $_reverifyPost := false;
}



// function declaration for _module._default.fib
function _module.__default.fib($ly: LayerType, n#0: int) : int;

function _module.__default.fib#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.fib($LS($ly), n#0) } 
  _module.__default.fib($LS($ly), n#0) == _module.__default.fib($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.fib(AsFuelBottom($ly), n#0) } 
  _module.__default.fib($ly, n#0) == _module.__default.fib($LZ, n#0));

// consequence axiom for _module.__default.fib
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.fib($ly, n#0) } 
    _module.__default.fib#canCall(n#0)
         || (17 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> LitInt(0) <= _module.__default.fib($ly, n#0));

function _module.__default.fib#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.fib
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.fib#requires($ly, n#0) } 
  LitInt(0) <= n#0 ==> _module.__default.fib#requires($ly, n#0) == true);

// definition axiom for _module.__default.fib (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.fib($LS($ly), n#0) } 
    _module.__default.fib#canCall(n#0)
         || (17 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (2 <= n#0
           ==> _module.__default.fib#canCall(n#0 - 1) && _module.__default.fib#canCall(n#0 - 2))
         && _module.__default.fib($LS($ly), n#0)
           == (if n#0 < 2
             then n#0
             else _module.__default.fib($ly, n#0 - 1) + _module.__default.fib($ly, n#0 - 2)));

// definition axiom for _module.__default.fib for all literals (revealed)
axiom 17 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.fib($LS($ly), LitInt(n#0)) } 
    _module.__default.fib#canCall(LitInt(n#0))
         || (17 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (!Lit(n#0 < 2)
           ==> _module.__default.fib#canCall(LitInt(n#0 - 1))
             && _module.__default.fib#canCall(LitInt(n#0 - 2)))
         && _module.__default.fib($LS($ly), LitInt(n#0))
           == (if n#0 < 2
             then n#0
             else _module.__default.fib($LS($ly), LitInt(n#0 - 1))
               + _module.__default.fib($LS($ly), LitInt(n#0 - 2))));

procedure CheckWellformed$$_module.__default.fib(n#0: int where LitInt(0) <= n#0);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.fib(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##n#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function fib
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(166,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.fib($LS($LZ), n#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 < 2)
        {
            assume _module.__default.fib($LS($LZ), n#0) == n#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.fib($LS($LZ), n#0), Tclass._System.nat());
        }
        else
        {
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.fib#canCall(n#0 - 1);
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#1 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#1 == n#0;
            assert ##n#1 < n#0;
            assume _module.__default.fib#canCall(n#0 - 2);
            assert $Is(_module.__default.fib($LS($LZ), n#0 - 1)
                 + _module.__default.fib($LS($LZ), n#0 - 2), 
              Tclass._System.nat());
            assume _module.__default.fib($LS($LZ), n#0)
               == _module.__default.fib($LS($LZ), n#0 - 1)
                 + _module.__default.fib($LS($LZ), n#0 - 2);
            assume _module.__default.fib#canCall(n#0 - 1) && _module.__default.fib#canCall(n#0 - 2);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.fib($LS($LZ), n#0), Tclass._System.nat());
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure CheckWellformed$$_module.__default.test__fib();
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.test__fib()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;

    // AddMethodImpl: test_fib, CheckWellformed$$_module.__default.test__fib
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(170,13): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(171,17): post-state"} true;
    assert $Is(LitInt(12), Tclass._System.nat());
    ##n#0 := LitInt(12);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.fib#canCall(LitInt(12));
    assume LitInt(_module.__default.fib($LS($LZ), LitInt(12))) == LitInt(144);
}



procedure Call$$_module.__default.test__fib();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.fib#canCall(LitInt(12));
  ensures LitInt(_module.__default.fib($LS($LS($LZ)), LitInt(12))) == LitInt(144);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.test__fib() returns ($_reverifyPost: bool);
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.fib#canCall(LitInt(12));
  ensures LitInt(_module.__default.fib($LS($LS($LZ)), LitInt(12))) == LitInt(144);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.test__fib() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: test_fib, Impl$$_module.__default.test__fib
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(172,0): initial state"} true;
    $_reverifyPost := false;
}



procedure {:_induction k#0} CheckWellformed$$_module.__default.test__fib1(k#0: int where LitInt(0) <= k#0);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction k#0} Call$$_module.__default.test__fib1(k#0: int where LitInt(0) <= k#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures k#0 == LitInt(12) ==> _module.__default.fib#canCall(k#0);
  ensures k#0 == LitInt(12) ==> _module.__default.fib($LS($LS($LZ)), k#0) == LitInt(144);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0} Impl$$_module.__default.test__fib1(k#0: int where LitInt(0) <= k#0) returns ($_reverifyPost: bool);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures k#0 == LitInt(12) ==> _module.__default.fib#canCall(k#0);
  ensures k#0 == LitInt(12) ==> _module.__default.fib($LS($LS($LZ)), k#0) == LitInt(144);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0} Impl$$_module.__default.test__fib1(k#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: test_fib1, Impl$$_module.__default.test__fib1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(176,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int :: 
      LitInt(0) <= $ih#k0#0 && Lit(true) && 0 <= $ih#k0#0 && $ih#k0#0 < k#0
         ==> 
        $ih#k0#0 == LitInt(12)
         ==> _module.__default.fib($LS($LZ), $ih#k0#0) == LitInt(144));
    $_reverifyPost := false;
}



procedure {:_induction k#0} CheckWellformed$$_module.__default.test__fib2(k#0: int where LitInt(0) <= k#0);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction k#0} Call$$_module.__default.test__fib2(k#0: int where LitInt(0) <= k#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures LitInt(12) <= k#0 ==> k#0 <= LitInt(12) ==> _module.__default.fib#canCall(k#0);
  ensures LitInt(12) <= k#0 && k#0 <= LitInt(12)
     ==> _module.__default.fib($LS($LS($LZ)), k#0) == LitInt(144);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction k#0} Impl$$_module.__default.test__fib2(k#0: int where LitInt(0) <= k#0) returns ($_reverifyPost: bool);
  free requires 19 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures LitInt(12) <= k#0 ==> k#0 <= LitInt(12) ==> _module.__default.fib#canCall(k#0);
  ensures LitInt(12) <= k#0 && k#0 <= LitInt(12)
     ==> _module.__default.fib($LS($LS($LZ)), k#0) == LitInt(144);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction k#0} Impl$$_module.__default.test__fib2(k#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: test_fib2, Impl$$_module.__default.test__fib2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(180,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#k0#0: int :: 
      LitInt(0) <= $ih#k0#0 && Lit(true) && 0 <= $ih#k0#0 && $ih#k0#0 < k#0
         ==> 
        LitInt(12) <= $ih#k0#0 && $ih#k0#0 <= LitInt(12)
         ==> _module.__default.fib($LS($LZ), $ih#k0#0) == LitInt(144));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.test__fib3(k#0: int where LitInt(0) <= k#0, m#0: int where LitInt(0) <= m#0);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.test__fib3(k#0: int where LitInt(0) <= k#0, m#0: int where LitInt(0) <= m#0);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.test__fib3(k#0: int where LitInt(0) <= k#0, m#0: int where LitInt(0) <= m#0)
   returns ($_reverifyPost: bool);
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.test__fib3(k#0: int, m#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var y#0: int;
  var ##n#0: int;

    // AddMethodImpl: test_fib3, Impl$$_module.__default.test__fib3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(183,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(184,9)
    assume true;
    assume true;
    y#0 := LitInt(12);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(184,13)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Computations.dfy(185,3)
    if (y#0 <= k#0)
    {
    }

    if (y#0 <= k#0 && k#0 < y#0 + m#0)
    {
    }

    if (y#0 <= k#0 && k#0 < y#0 + m#0 && m#0 == LitInt(1))
    {
        ##n#0 := k#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
        assume _module.__default.fib#canCall(k#0);
    }

    assume y#0 <= k#0
       ==> 
      k#0 < y#0 + m#0
       ==> 
      m#0 == LitInt(1)
       ==> _module.__default.fib#canCall(k#0);
    assert {:subsumption 0} y#0 <= k#0 && k#0 < y#0 + m#0 && m#0 == LitInt(1)
       ==> _module.__default.fib($LS($LS($LZ)), k#0) == LitInt(144);
    assume y#0 <= k#0 && k#0 < y#0 + m#0 && m#0 == LitInt(1)
       ==> _module.__default.fib($LS($LZ), k#0) == LitInt(144);
}



const unique class.NeedsAllLiteralsAxiom.__default: ClassName;

function Tclass.NeedsAllLiteralsAxiom.__default() : Ty;

const unique Tagclass.NeedsAllLiteralsAxiom.__default: TyTag;

// Tclass.NeedsAllLiteralsAxiom.__default Tag
axiom Tag(Tclass.NeedsAllLiteralsAxiom.__default())
     == Tagclass.NeedsAllLiteralsAxiom.__default
   && TagFamily(Tclass.NeedsAllLiteralsAxiom.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.NeedsAllLiteralsAxiom.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.NeedsAllLiteralsAxiom.__default()) } 
  $IsBox(bx, Tclass.NeedsAllLiteralsAxiom.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.NeedsAllLiteralsAxiom.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.NeedsAllLiteralsAxiom.__default()) } 
  $Is($o, Tclass.NeedsAllLiteralsAxiom.__default())
     <==> $o == null || dtype($o) == Tclass.NeedsAllLiteralsAxiom.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.NeedsAllLiteralsAxiom.__default(), $h) } 
  $IsAlloc($o, Tclass.NeedsAllLiteralsAxiom.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for NeedsAllLiteralsAxiom._default.trick
function NeedsAllLiteralsAxiom.__default.trick($ly: LayerType, n#0: int, m#0: int) : int;

function NeedsAllLiteralsAxiom.__default.trick#canCall(n#0: int, m#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int, m#0: int :: 
  { NeedsAllLiteralsAxiom.__default.trick($LS($ly), n#0, m#0) } 
  NeedsAllLiteralsAxiom.__default.trick($LS($ly), n#0, m#0)
     == NeedsAllLiteralsAxiom.__default.trick($ly, n#0, m#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int, m#0: int :: 
  { NeedsAllLiteralsAxiom.__default.trick(AsFuelBottom($ly), n#0, m#0) } 
  NeedsAllLiteralsAxiom.__default.trick($ly, n#0, m#0)
     == NeedsAllLiteralsAxiom.__default.trick($LZ, n#0, m#0));

// consequence axiom for NeedsAllLiteralsAxiom.__default.trick
axiom true
   ==> (forall $ly: LayerType, n#0: int, m#0: int :: 
    { NeedsAllLiteralsAxiom.__default.trick($ly, n#0, m#0) } 
    NeedsAllLiteralsAxiom.__default.trick#canCall(n#0, m#0)
         || (LitInt(0) <= n#0 && LitInt(0) <= m#0)
       ==> LitInt(0) <= NeedsAllLiteralsAxiom.__default.trick($ly, n#0, m#0));

function NeedsAllLiteralsAxiom.__default.trick#requires(LayerType, int, int) : bool;

// #requires axiom for NeedsAllLiteralsAxiom.__default.trick
axiom (forall $ly: LayerType, n#0: int, m#0: int :: 
  { NeedsAllLiteralsAxiom.__default.trick#requires($ly, n#0, m#0) } 
  LitInt(0) <= n#0 && LitInt(0) <= m#0
     ==> NeedsAllLiteralsAxiom.__default.trick#requires($ly, n#0, m#0) == true);

// definition axiom for NeedsAllLiteralsAxiom.__default.trick (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: int, m#0: int :: 
    { NeedsAllLiteralsAxiom.__default.trick($LS($ly), n#0, m#0) } 
    NeedsAllLiteralsAxiom.__default.trick#canCall(n#0, m#0)
         || (LitInt(0) <= n#0 && LitInt(0) <= m#0)
       ==> (!(n#0 < m#0 || m#0 == LitInt(0))
           ==> NeedsAllLiteralsAxiom.__default.trick#canCall(n#0 - m#0, m#0))
         && NeedsAllLiteralsAxiom.__default.trick($LS($ly), n#0, m#0)
           == (if n#0 < m#0 || m#0 == LitInt(0)
             then n#0
             else NeedsAllLiteralsAxiom.__default.trick($ly, n#0 - m#0, m#0) + m#0));

// definition axiom for NeedsAllLiteralsAxiom.__default.trick for decreasing-related literals (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: int, m#0: int :: 
    {:weight 3} { NeedsAllLiteralsAxiom.__default.trick($LS($ly), LitInt(n#0), m#0) } 
    NeedsAllLiteralsAxiom.__default.trick#canCall(LitInt(n#0), m#0)
         || (LitInt(0) <= n#0 && LitInt(0) <= m#0)
       ==> (!(n#0 < m#0 || m#0 == LitInt(0))
           ==> NeedsAllLiteralsAxiom.__default.trick#canCall(n#0 - m#0, m#0))
         && NeedsAllLiteralsAxiom.__default.trick($LS($ly), LitInt(n#0), m#0)
           == (if n#0 < m#0 || m#0 == LitInt(0)
             then n#0
             else NeedsAllLiteralsAxiom.__default.trick($LS($ly), n#0 - m#0, m#0) + m#0));

// definition axiom for NeedsAllLiteralsAxiom.__default.trick for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: int, m#0: int :: 
    {:weight 3} { NeedsAllLiteralsAxiom.__default.trick($LS($ly), LitInt(n#0), LitInt(m#0)) } 
    NeedsAllLiteralsAxiom.__default.trick#canCall(LitInt(n#0), LitInt(m#0))
         || (LitInt(0) <= n#0 && LitInt(0) <= m#0)
       ==> (!(n#0 < m#0 || LitInt(m#0) == LitInt(0))
           ==> NeedsAllLiteralsAxiom.__default.trick#canCall(LitInt(n#0 - m#0), LitInt(m#0)))
         && NeedsAllLiteralsAxiom.__default.trick($LS($ly), LitInt(n#0), LitInt(m#0))
           == (if n#0 < m#0 || LitInt(m#0) == LitInt(0)
             then n#0
             else NeedsAllLiteralsAxiom.__default.trick($LS($ly), LitInt(n#0 - m#0), LitInt(m#0))
               + m#0));

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

const unique tytagFamily$intlist: TyTagFamily;

const unique tytagFamily$list: TyTagFamily;

const unique tytagFamily$exp: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
