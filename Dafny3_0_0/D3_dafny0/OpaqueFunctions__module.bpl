// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy -print:./OpaqueFunctions.bpl

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

const BaseFuel_OpaqueFunctionsAreNotInlined._default.F: LayerType;

const StartFuel_OpaqueFunctionsAreNotInlined._default.F: LayerType;

const StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F: LayerType;

const BaseFuel_M0._default.F: LayerType;

const StartFuel_M0._default.F: LayerType;

const StartFuelAssert_M0._default.F: LayerType;

const BaseFuel_M1._default.F: LayerType;

const StartFuel_M1._default.F: LayerType;

const StartFuelAssert_M1._default.F: LayerType;

const BaseFuel_LayerQuantifiers._default.f: LayerType;

const StartFuel_LayerQuantifiers._default.f: LayerType;

const StartFuelAssert_LayerQuantifiers._default.f: LayerType;

const BaseFuel_Regression._default.Length: LayerType;

const StartFuel_Regression._default.Length: LayerType;

const StartFuelAssert_Regression._default.Length: LayerType;

const BaseFuel_TypeMembers.Tr.IsFavorite: LayerType;

const StartFuel_TypeMembers.Tr.IsFavorite: LayerType;

const StartFuelAssert_TypeMembers.Tr.IsFavorite: LayerType;

const BaseFuel_TypeMembers.Tr.IsFive: LayerType;

const StartFuel_TypeMembers.Tr.IsFive: LayerType;

const StartFuelAssert_TypeMembers.Tr.IsFive: LayerType;

const BaseFuel_TypeMembers.Color.IsFavorite: LayerType;

const StartFuel_TypeMembers.Color.IsFavorite: LayerType;

const StartFuelAssert_TypeMembers.Color.IsFavorite: LayerType;

const BaseFuel_TypeMembers.Color.IsFive: LayerType;

const StartFuel_TypeMembers.Color.IsFive: LayerType;

const StartFuelAssert_TypeMembers.Color.IsFive: LayerType;

const BaseFuel_TypeMembers.Small.IsFavorite: LayerType;

const StartFuel_TypeMembers.Small.IsFavorite: LayerType;

const StartFuelAssert_TypeMembers.Small.IsFavorite: LayerType;

const BaseFuel_TypeMembers.Small.IsFive: LayerType;

const StartFuel_TypeMembers.Small.IsFive: LayerType;

const StartFuelAssert_TypeMembers.Small.IsFive: LayerType;

const BaseFuel__module._default.id: LayerType;

const StartFuel__module._default.id: LayerType;

const StartFuelAssert__module._default.id: LayerType;

const BaseFuel__module._default.id_box: LayerType;

const StartFuel__module._default.id_box: LayerType;

const StartFuelAssert__module._default.id_box: LayerType;

const BaseFuel__module._default.zero: LayerType;

const StartFuel__module._default.zero: LayerType;

const StartFuelAssert__module._default.zero: LayerType;

// Constructor function declaration
function #_module.Box.Bx(Box) : DatatypeType;

const unique ##_module.Box.Bx: DtCtorId;

// Constructor identifier
axiom (forall a#14#0#0: Box :: 
  { #_module.Box.Bx(a#14#0#0) } 
  DatatypeCtorId(#_module.Box.Bx(a#14#0#0)) == ##_module.Box.Bx);

function _module.Box.Bx_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.Box.Bx_q(d) } 
  _module.Box.Bx_q(d) <==> DatatypeCtorId(d) == ##_module.Box.Bx);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.Box.Bx_q(d) } 
  _module.Box.Bx_q(d) ==> (exists a#15#0#0: Box :: d == #_module.Box.Bx(a#15#0#0)));

function Tclass._module.Box(Ty) : Ty;

const unique Tagclass._module.Box: TyTag;

// Tclass._module.Box Tag
axiom (forall _module.Box$A: Ty :: 
  { Tclass._module.Box(_module.Box$A) } 
  Tag(Tclass._module.Box(_module.Box$A)) == Tagclass._module.Box
     && TagFamily(Tclass._module.Box(_module.Box$A)) == tytagFamily$Box);

// Tclass._module.Box injectivity 0
axiom (forall _module.Box$A: Ty :: 
  { Tclass._module.Box(_module.Box$A) } 
  Tclass._module.Box_0(Tclass._module.Box(_module.Box$A)) == _module.Box$A);

function Tclass._module.Box_0(Ty) : Ty;

// Box/unbox axiom for Tclass._module.Box
axiom (forall _module.Box$A: Ty, bx: Box :: 
  { $IsBox(bx, Tclass._module.Box(_module.Box$A)) } 
  $IsBox(bx, Tclass._module.Box(_module.Box$A))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass._module.Box(_module.Box$A)));

// Constructor $Is
axiom (forall _module.Box$A: Ty, a#16#0#0: Box :: 
  { $Is(#_module.Box.Bx(a#16#0#0), Tclass._module.Box(_module.Box$A)) } 
  $Is(#_module.Box.Bx(a#16#0#0), Tclass._module.Box(_module.Box$A))
     <==> $IsBox(a#16#0#0, _module.Box$A));

// Constructor $IsAlloc
axiom (forall _module.Box$A: Ty, a#17#0#0: Box, $h: Heap :: 
  { $IsAlloc(#_module.Box.Bx(a#17#0#0), Tclass._module.Box(_module.Box$A), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Box.Bx(a#17#0#0), Tclass._module.Box(_module.Box$A), $h)
       <==> $IsAllocBox(a#17#0#0, _module.Box$A, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.Box$A: Ty, $h: Heap :: 
  { $IsAllocBox(_module.Box._h0(d), _module.Box$A, $h) } 
  $IsGoodHeap($h)
       && 
      _module.Box.Bx_q(d)
       && $IsAlloc(d, Tclass._module.Box(_module.Box$A), $h)
     ==> $IsAllocBox(_module.Box._h0(d), _module.Box$A, $h));

// Constructor literal
axiom (forall a#18#0#0: Box :: 
  { #_module.Box.Bx(Lit(a#18#0#0)) } 
  #_module.Box.Bx(Lit(a#18#0#0)) == Lit(#_module.Box.Bx(a#18#0#0)));

function _module.Box._h0(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#19#0#0: Box :: 
  { #_module.Box.Bx(a#19#0#0) } 
  _module.Box._h0(#_module.Box.Bx(a#19#0#0)) == a#19#0#0);

// Inductive rank
axiom (forall a#20#0#0: Box :: 
  { #_module.Box.Bx(a#20#0#0) } 
  BoxRank(a#20#0#0) < DtRank(#_module.Box.Bx(a#20#0#0)));

// Depth-one case-split function
function $IsA#_module.Box(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.Box(d) } 
  $IsA#_module.Box(d) ==> _module.Box.Bx_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.Box$A: Ty, d: DatatypeType :: 
  { _module.Box.Bx_q(d), $Is(d, Tclass._module.Box(_module.Box$A)) } 
  $Is(d, Tclass._module.Box(_module.Box$A)) ==> _module.Box.Bx_q(d));

// Datatype extensional equality declaration
function _module.Box#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.Box.Bx
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Box#Equal(a, b) } 
  true ==> (_module.Box#Equal(a, b) <==> _module.Box._h0(a) == _module.Box._h0(b)));

// Datatype extensionality axiom: _module.Box
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.Box#Equal(a, b) } 
  _module.Box#Equal(a, b) <==> a == b);

const unique class._module.Box: ClassName;

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

// function declaration for _module._default.id
function _module.__default.id(_module._default.id$A: Ty, $ly: LayerType, x#0: Box) : Box;

function _module.__default.id#canCall(_module._default.id$A: Ty, x#0: Box) : bool;

// layer synonym axiom
axiom (forall _module._default.id$A: Ty, $ly: LayerType, x#0: Box :: 
  { _module.__default.id(_module._default.id$A, $LS($ly), x#0) } 
  _module.__default.id(_module._default.id$A, $LS($ly), x#0)
     == _module.__default.id(_module._default.id$A, $ly, x#0));

// fuel synonym axiom
axiom (forall _module._default.id$A: Ty, $ly: LayerType, x#0: Box :: 
  { _module.__default.id(_module._default.id$A, AsFuelBottom($ly), x#0) } 
  _module.__default.id(_module._default.id$A, $ly, x#0)
     == _module.__default.id(_module._default.id$A, $LZ, x#0));

// consequence axiom for _module.__default.id
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.id$A: Ty, $ly: LayerType, x#0: Box :: 
    { _module.__default.id(_module._default.id$A, $ly, x#0) } 
    _module.__default.id#canCall(_module._default.id$A, x#0)
         || (3 != $FunctionContextHeight && $IsBox(x#0, _module._default.id$A))
       ==> $IsBox(_module.__default.id(_module._default.id$A, $ly, x#0), _module._default.id$A));

function _module.__default.id#requires(Ty, LayerType, Box) : bool;

// #requires axiom for _module.__default.id
axiom (forall _module._default.id$A: Ty, $ly: LayerType, x#0: Box :: 
  { _module.__default.id#requires(_module._default.id$A, $ly, x#0) } 
  $IsBox(x#0, _module._default.id$A)
     ==> _module.__default.id#requires(_module._default.id$A, $ly, x#0) == true);

// definition axiom for _module.__default.id (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.id$A: Ty, $ly: LayerType, x#0: Box :: 
    { _module.__default.id(_module._default.id$A, $LS($ly), x#0) } 
    _module.__default.id#canCall(_module._default.id$A, x#0)
         || (3 != $FunctionContextHeight && $IsBox(x#0, _module._default.id$A))
       ==> _module.__default.id(_module._default.id$A, $LS($ly), x#0) == x#0);

// definition axiom for _module.__default.id for all literals (revealed)
axiom 3 <= $FunctionContextHeight
   ==> (forall _module._default.id$A: Ty, $ly: LayerType, x#0: Box :: 
    {:weight 3} { _module.__default.id(_module._default.id$A, $LS($ly), Lit(x#0)) } 
    _module.__default.id#canCall(_module._default.id$A, Lit(x#0))
         || (3 != $FunctionContextHeight && $IsBox(x#0, _module._default.id$A))
       ==> _module.__default.id(_module._default.id$A, $LS($ly), Lit(x#0)) == Lit(x#0));

procedure {:opaque} CheckWellformed$$_module.__default.id(_module._default.id$A: Ty, x#0: Box where $IsBox(x#0, _module._default.id$A));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.id__ok();
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.id__ok();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.id__ok() returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.id__ok() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;

    // AddMethodImpl: id_ok, Impl$$_module.__default.id__ok
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueFunctionsAreNotInlined._default.F)
       == StartFuel_OpaqueFunctionsAreNotInlined._default.F;
    assume AsFuelBottom(StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F)
       == StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F;
    assume AsFuelBottom(StartFuel_M0._default.F) == StartFuel_M0._default.F;
    assume AsFuelBottom(StartFuelAssert_M0._default.F) == StartFuelAssert_M0._default.F;
    assume AsFuelBottom(StartFuel_M1._default.F) == StartFuel_M1._default.F;
    assume AsFuelBottom(StartFuelAssert_M1._default.F) == StartFuelAssert_M1._default.F;
    assume AsFuelBottom(StartFuel_LayerQuantifiers._default.f)
       == StartFuel_LayerQuantifiers._default.f;
    assume AsFuelBottom(StartFuelAssert_LayerQuantifiers._default.f)
       == StartFuelAssert_LayerQuantifiers._default.f;
    assume AsFuelBottom(StartFuel_Regression._default.Length)
       == StartFuel_Regression._default.Length;
    assume AsFuelBottom(StartFuelAssert_Regression._default.Length)
       == StartFuelAssert_Regression._default.Length;
    assume AsFuelBottom(StartFuel_TypeMembers.Tr.IsFavorite)
       == StartFuel_TypeMembers.Tr.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Tr.IsFavorite)
       == StartFuelAssert_TypeMembers.Tr.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Tr.IsFive) == StartFuel_TypeMembers.Tr.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Tr.IsFive)
       == StartFuelAssert_TypeMembers.Tr.IsFive;
    assume AsFuelBottom(StartFuel_TypeMembers.Color.IsFavorite)
       == StartFuel_TypeMembers.Color.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Color.IsFavorite)
       == StartFuelAssert_TypeMembers.Color.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Color.IsFive)
       == StartFuel_TypeMembers.Color.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Color.IsFive)
       == StartFuelAssert_TypeMembers.Color.IsFive;
    assume AsFuelBottom(StartFuel_TypeMembers.Small.IsFavorite)
       == StartFuel_TypeMembers.Small.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Small.IsFavorite)
       == StartFuelAssert_TypeMembers.Small.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Small.IsFive)
       == StartFuel_TypeMembers.Small.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Small.IsFive)
       == StartFuelAssert_TypeMembers.Small.IsFive;
    assume AsFuelBottom(StartFuel__module._default.id) == StartFuel__module._default.id;
    assume AsFuelBottom(StartFuelAssert__module._default.id)
       == StartFuelAssert__module._default.id;
    assume AsFuelBottom(StartFuel__module._default.id_box)
       == StartFuel__module._default.id_box;
    assume AsFuelBottom(StartFuelAssert__module._default.id_box)
       == StartFuelAssert__module._default.id_box;
    assume AsFuelBottom(StartFuel__module._default.zero) == StartFuel__module._default.zero;
    assume AsFuelBottom(StartFuelAssert__module._default.zero)
       == StartFuelAssert__module._default.zero;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(207,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(208,3)
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(208,12)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.reveal__id();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(208,13)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(209,3)
    ##x#0 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, TInt, $Heap);
    assume _module.__default.id#canCall(TInt, $Box(LitInt(1)));
    assume _module.__default.id#canCall(TInt, $Box(LitInt(1)));
    assert {:subsumption 0} $Unbox(_module.__default.id(TInt, StartFuelAssert__module._default.id, $Box(LitInt(1)))): int
       == LitInt(1);
    assume $Unbox(_module.__default.id(TInt, StartFuel__module._default.id, $Box(LitInt(1)))): int
       == LitInt(1);
}



procedure CheckWellformed$$_module.__default.id__fail();
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.id__fail();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.id__fail() returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.id__fail() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: int;

    // AddMethodImpl: id_fail, Impl$$_module.__default.id__fail
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueFunctionsAreNotInlined._default.F)
       == StartFuel_OpaqueFunctionsAreNotInlined._default.F;
    assume AsFuelBottom(StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F)
       == StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F;
    assume AsFuelBottom(StartFuel_M0._default.F) == StartFuel_M0._default.F;
    assume AsFuelBottom(StartFuelAssert_M0._default.F) == StartFuelAssert_M0._default.F;
    assume AsFuelBottom(StartFuel_M1._default.F) == StartFuel_M1._default.F;
    assume AsFuelBottom(StartFuelAssert_M1._default.F) == StartFuelAssert_M1._default.F;
    assume AsFuelBottom(StartFuel_LayerQuantifiers._default.f)
       == StartFuel_LayerQuantifiers._default.f;
    assume AsFuelBottom(StartFuelAssert_LayerQuantifiers._default.f)
       == StartFuelAssert_LayerQuantifiers._default.f;
    assume AsFuelBottom(StartFuel_Regression._default.Length)
       == StartFuel_Regression._default.Length;
    assume AsFuelBottom(StartFuelAssert_Regression._default.Length)
       == StartFuelAssert_Regression._default.Length;
    assume AsFuelBottom(StartFuel_TypeMembers.Tr.IsFavorite)
       == StartFuel_TypeMembers.Tr.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Tr.IsFavorite)
       == StartFuelAssert_TypeMembers.Tr.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Tr.IsFive) == StartFuel_TypeMembers.Tr.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Tr.IsFive)
       == StartFuelAssert_TypeMembers.Tr.IsFive;
    assume AsFuelBottom(StartFuel_TypeMembers.Color.IsFavorite)
       == StartFuel_TypeMembers.Color.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Color.IsFavorite)
       == StartFuelAssert_TypeMembers.Color.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Color.IsFive)
       == StartFuel_TypeMembers.Color.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Color.IsFive)
       == StartFuelAssert_TypeMembers.Color.IsFive;
    assume AsFuelBottom(StartFuel_TypeMembers.Small.IsFavorite)
       == StartFuel_TypeMembers.Small.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Small.IsFavorite)
       == StartFuelAssert_TypeMembers.Small.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Small.IsFive)
       == StartFuel_TypeMembers.Small.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Small.IsFive)
       == StartFuelAssert_TypeMembers.Small.IsFive;
    assume AsFuelBottom(StartFuel__module._default.id) == StartFuel__module._default.id;
    assume AsFuelBottom(StartFuelAssert__module._default.id)
       == StartFuelAssert__module._default.id;
    assume AsFuelBottom(StartFuel__module._default.id_box)
       == StartFuel__module._default.id_box;
    assume AsFuelBottom(StartFuelAssert__module._default.id_box)
       == StartFuelAssert__module._default.id_box;
    assume AsFuelBottom(StartFuel__module._default.zero) == StartFuel__module._default.zero;
    assume AsFuelBottom(StartFuelAssert__module._default.zero)
       == StartFuelAssert__module._default.zero;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(213,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(214,3)
    ##x#0 := LitInt(1);
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, TInt, $Heap);
    assume _module.__default.id#canCall(TInt, $Box(LitInt(1)));
    assume _module.__default.id#canCall(TInt, $Box(LitInt(1)));
    assert {:subsumption 0} $Unbox(_module.__default.id(TInt, StartFuelAssert__module._default.id, $Box(LitInt(1)))): int
       == LitInt(1);
    assume $Unbox(_module.__default.id(TInt, StartFuel__module._default.id, $Box(LitInt(1)))): int
       == LitInt(1);
}



// function declaration for _module._default.id_box
function _module.__default.id__box(_module._default.id_box$_T0: Ty, $ly: LayerType, x#0: DatatypeType)
   : DatatypeType;

function _module.__default.id__box#canCall(_module._default.id_box$_T0: Ty, x#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.id_box$_T0: Ty, $ly: LayerType, x#0: DatatypeType :: 
  { _module.__default.id__box(_module._default.id_box$_T0, $LS($ly), x#0) } 
  _module.__default.id__box(_module._default.id_box$_T0, $LS($ly), x#0)
     == _module.__default.id__box(_module._default.id_box$_T0, $ly, x#0));

// fuel synonym axiom
axiom (forall _module._default.id_box$_T0: Ty, $ly: LayerType, x#0: DatatypeType :: 
  { _module.__default.id__box(_module._default.id_box$_T0, AsFuelBottom($ly), x#0) } 
  _module.__default.id__box(_module._default.id_box$_T0, $ly, x#0)
     == _module.__default.id__box(_module._default.id_box$_T0, $LZ, x#0));

// consequence axiom for _module.__default.id__box
axiom 1 <= $FunctionContextHeight
   ==> (forall _module._default.id_box$_T0: Ty, $ly: LayerType, x#0: DatatypeType :: 
    { _module.__default.id__box(_module._default.id_box$_T0, $ly, x#0) } 
    _module.__default.id__box#canCall(_module._default.id_box$_T0, x#0)
         || (1 != $FunctionContextHeight
           && $Is(x#0, Tclass._module.Box(_module._default.id_box$_T0)))
       ==> $Is(_module.__default.id__box(_module._default.id_box$_T0, $ly, x#0), 
        Tclass._module.Box(_module._default.id_box$_T0)));

function _module.__default.id__box#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.id__box
axiom (forall _module._default.id_box$_T0: Ty, $ly: LayerType, x#0: DatatypeType :: 
  { _module.__default.id__box#requires(_module._default.id_box$_T0, $ly, x#0) } 
  $Is(x#0, Tclass._module.Box(_module._default.id_box$_T0))
     ==> _module.__default.id__box#requires(_module._default.id_box$_T0, $ly, x#0)
       == true);

// definition axiom for _module.__default.id__box (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module._default.id_box$_T0: Ty, $ly: LayerType, x#0: DatatypeType :: 
    { _module.__default.id__box(_module._default.id_box$_T0, $LS($ly), x#0) } 
    _module.__default.id__box#canCall(_module._default.id_box$_T0, x#0)
         || (1 != $FunctionContextHeight
           && $Is(x#0, Tclass._module.Box(_module._default.id_box$_T0)))
       ==> _module.__default.id__box(_module._default.id_box$_T0, $LS($ly), x#0) == x#0);

// definition axiom for _module.__default.id__box for all literals (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall _module._default.id_box$_T0: Ty, $ly: LayerType, x#0: DatatypeType :: 
    {:weight 3} { _module.__default.id__box(_module._default.id_box$_T0, $LS($ly), Lit(x#0)) } 
    _module.__default.id__box#canCall(_module._default.id_box$_T0, Lit(x#0))
         || (1 != $FunctionContextHeight
           && $Is(x#0, Tclass._module.Box(_module._default.id_box$_T0)))
       ==> _module.__default.id__box(_module._default.id_box$_T0, $LS($ly), Lit(x#0))
         == Lit(x#0));

procedure {:opaque} CheckWellformed$$_module.__default.id__box(_module._default.id_box$_T0: Ty, 
    x#0: DatatypeType
       where $Is(x#0, Tclass._module.Box(_module._default.id_box$_T0)));
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure CheckWellformed$$_module.__default.box__ok();
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.box__ok();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.box__ok() returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.box__ok() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: DatatypeType;

    // AddMethodImpl: box_ok, Impl$$_module.__default.box__ok
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueFunctionsAreNotInlined._default.F)
       == StartFuel_OpaqueFunctionsAreNotInlined._default.F;
    assume AsFuelBottom(StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F)
       == StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F;
    assume AsFuelBottom(StartFuel_M0._default.F) == StartFuel_M0._default.F;
    assume AsFuelBottom(StartFuelAssert_M0._default.F) == StartFuelAssert_M0._default.F;
    assume AsFuelBottom(StartFuel_M1._default.F) == StartFuel_M1._default.F;
    assume AsFuelBottom(StartFuelAssert_M1._default.F) == StartFuelAssert_M1._default.F;
    assume AsFuelBottom(StartFuel_LayerQuantifiers._default.f)
       == StartFuel_LayerQuantifiers._default.f;
    assume AsFuelBottom(StartFuelAssert_LayerQuantifiers._default.f)
       == StartFuelAssert_LayerQuantifiers._default.f;
    assume AsFuelBottom(StartFuel_Regression._default.Length)
       == StartFuel_Regression._default.Length;
    assume AsFuelBottom(StartFuelAssert_Regression._default.Length)
       == StartFuelAssert_Regression._default.Length;
    assume AsFuelBottom(StartFuel_TypeMembers.Tr.IsFavorite)
       == StartFuel_TypeMembers.Tr.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Tr.IsFavorite)
       == StartFuelAssert_TypeMembers.Tr.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Tr.IsFive) == StartFuel_TypeMembers.Tr.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Tr.IsFive)
       == StartFuelAssert_TypeMembers.Tr.IsFive;
    assume AsFuelBottom(StartFuel_TypeMembers.Color.IsFavorite)
       == StartFuel_TypeMembers.Color.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Color.IsFavorite)
       == StartFuelAssert_TypeMembers.Color.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Color.IsFive)
       == StartFuel_TypeMembers.Color.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Color.IsFive)
       == StartFuelAssert_TypeMembers.Color.IsFive;
    assume AsFuelBottom(StartFuel_TypeMembers.Small.IsFavorite)
       == StartFuel_TypeMembers.Small.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Small.IsFavorite)
       == StartFuelAssert_TypeMembers.Small.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Small.IsFive)
       == StartFuel_TypeMembers.Small.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Small.IsFive)
       == StartFuelAssert_TypeMembers.Small.IsFive;
    assume AsFuelBottom(StartFuel__module._default.id) == StartFuel__module._default.id;
    assume AsFuelBottom(StartFuelAssert__module._default.id)
       == StartFuelAssert__module._default.id;
    assume AsFuelBottom(StartFuel__module._default.id_box)
       == StartFuel__module._default.id_box;
    assume AsFuelBottom(StartFuelAssert__module._default.id_box)
       == StartFuelAssert__module._default.id_box;
    assume AsFuelBottom(StartFuel__module._default.zero) == StartFuel__module._default.zero;
    assume AsFuelBottom(StartFuelAssert__module._default.zero)
       == StartFuelAssert__module._default.zero;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(222,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(223,3)
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(223,12)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.reveal__id();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(223,13)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(224,3)
    ##x#0 := Lit(#_module.Box.Bx($Box(LitInt(1))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, Tclass._module.Box(TInt), $Heap);
    assume _module.__default.id#canCall(Tclass._module.Box(TInt), $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))));
    assume _module.Box.Bx_q($Unbox(_module.__default.id(Tclass._module.Box(TInt), 
          StartFuel__module._default.id, 
          $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))))): DatatypeType);
    assume $IsA#_module.Box($Unbox(_module.__default.id(Tclass._module.Box(TInt), 
            StartFuel__module._default.id, 
            $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))))): DatatypeType)
       && _module.__default.id#canCall(Tclass._module.Box(TInt), $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))));
    assert {:subsumption 0} _module.Box#Equal($Unbox(_module.__default.id(Tclass._module.Box(TInt), 
          StartFuelAssert__module._default.id, 
          $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))))): DatatypeType, 
      #_module.Box.Bx($Box(LitInt(1))));
    assume _module.Box#Equal($Unbox(_module.__default.id(Tclass._module.Box(TInt), 
          StartFuel__module._default.id, 
          $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))))): DatatypeType, 
      #_module.Box.Bx($Box(LitInt(1))));
}



procedure CheckWellformed$$_module.__default.box__fail();
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.box__fail();
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.box__fail() returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.box__fail() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##x#0: DatatypeType;

    // AddMethodImpl: box_fail, Impl$$_module.__default.box__fail
    // initialize fuel constant
    assume AsFuelBottom(StartFuel_OpaqueFunctionsAreNotInlined._default.F)
       == StartFuel_OpaqueFunctionsAreNotInlined._default.F;
    assume AsFuelBottom(StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F)
       == StartFuelAssert_OpaqueFunctionsAreNotInlined._default.F;
    assume AsFuelBottom(StartFuel_M0._default.F) == StartFuel_M0._default.F;
    assume AsFuelBottom(StartFuelAssert_M0._default.F) == StartFuelAssert_M0._default.F;
    assume AsFuelBottom(StartFuel_M1._default.F) == StartFuel_M1._default.F;
    assume AsFuelBottom(StartFuelAssert_M1._default.F) == StartFuelAssert_M1._default.F;
    assume AsFuelBottom(StartFuel_LayerQuantifiers._default.f)
       == StartFuel_LayerQuantifiers._default.f;
    assume AsFuelBottom(StartFuelAssert_LayerQuantifiers._default.f)
       == StartFuelAssert_LayerQuantifiers._default.f;
    assume AsFuelBottom(StartFuel_Regression._default.Length)
       == StartFuel_Regression._default.Length;
    assume AsFuelBottom(StartFuelAssert_Regression._default.Length)
       == StartFuelAssert_Regression._default.Length;
    assume AsFuelBottom(StartFuel_TypeMembers.Tr.IsFavorite)
       == StartFuel_TypeMembers.Tr.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Tr.IsFavorite)
       == StartFuelAssert_TypeMembers.Tr.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Tr.IsFive) == StartFuel_TypeMembers.Tr.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Tr.IsFive)
       == StartFuelAssert_TypeMembers.Tr.IsFive;
    assume AsFuelBottom(StartFuel_TypeMembers.Color.IsFavorite)
       == StartFuel_TypeMembers.Color.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Color.IsFavorite)
       == StartFuelAssert_TypeMembers.Color.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Color.IsFive)
       == StartFuel_TypeMembers.Color.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Color.IsFive)
       == StartFuelAssert_TypeMembers.Color.IsFive;
    assume AsFuelBottom(StartFuel_TypeMembers.Small.IsFavorite)
       == StartFuel_TypeMembers.Small.IsFavorite;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Small.IsFavorite)
       == StartFuelAssert_TypeMembers.Small.IsFavorite;
    assume AsFuelBottom(StartFuel_TypeMembers.Small.IsFive)
       == StartFuel_TypeMembers.Small.IsFive;
    assume AsFuelBottom(StartFuelAssert_TypeMembers.Small.IsFive)
       == StartFuelAssert_TypeMembers.Small.IsFive;
    assume AsFuelBottom(StartFuel__module._default.id) == StartFuel__module._default.id;
    assume AsFuelBottom(StartFuelAssert__module._default.id)
       == StartFuelAssert__module._default.id;
    assume AsFuelBottom(StartFuel__module._default.id_box)
       == StartFuel__module._default.id_box;
    assume AsFuelBottom(StartFuelAssert__module._default.id_box)
       == StartFuelAssert__module._default.id_box;
    assume AsFuelBottom(StartFuel__module._default.zero) == StartFuel__module._default.zero;
    assume AsFuelBottom(StartFuelAssert__module._default.zero)
       == StartFuelAssert__module._default.zero;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(228,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/OpaqueFunctions.dfy(229,3)
    ##x#0 := Lit(#_module.Box.Bx($Box(LitInt(1))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##x#0, Tclass._module.Box(TInt), $Heap);
    assume _module.__default.id#canCall(Tclass._module.Box(TInt), $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))));
    assume _module.Box.Bx_q($Unbox(_module.__default.id(Tclass._module.Box(TInt), 
          StartFuel__module._default.id, 
          $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))))): DatatypeType);
    assume $IsA#_module.Box($Unbox(_module.__default.id(Tclass._module.Box(TInt), 
            StartFuel__module._default.id, 
            $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))))): DatatypeType)
       && _module.__default.id#canCall(Tclass._module.Box(TInt), $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))));
    assert {:subsumption 0} _module.Box#Equal($Unbox(_module.__default.id(Tclass._module.Box(TInt), 
          StartFuelAssert__module._default.id, 
          $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))))): DatatypeType, 
      #_module.Box.Bx($Box(LitInt(1))));
    assume _module.Box#Equal($Unbox(_module.__default.id(Tclass._module.Box(TInt), 
          StartFuel__module._default.id, 
          $Box(Lit(#_module.Box.Bx($Box(LitInt(1))))))): DatatypeType, 
      #_module.Box.Bx($Box(LitInt(1))));
}



// function declaration for _module._default.zero
function _module.__default.zero(_module._default.zero$A: Ty, $ly: LayerType) : int;

function _module.__default.zero#canCall(_module._default.zero$A: Ty) : bool;

// layer synonym axiom
axiom (forall _module._default.zero$A: Ty, $ly: LayerType :: 
  { _module.__default.zero(_module._default.zero$A, $LS($ly)) } 
  _module.__default.zero(_module._default.zero$A, $LS($ly))
     == _module.__default.zero(_module._default.zero$A, $ly));

// fuel synonym axiom
axiom (forall _module._default.zero$A: Ty, $ly: LayerType :: 
  { _module.__default.zero(_module._default.zero$A, AsFuelBottom($ly)) } 
  _module.__default.zero(_module._default.zero$A, $ly)
     == _module.__default.zero(_module._default.zero$A, $LZ));

// consequence axiom for _module.__default.zero
axiom 8 <= $FunctionContextHeight
   ==> (forall _module._default.zero$A: Ty, $ly: LayerType :: 
    { _module.__default.zero(_module._default.zero$A, $ly) } 
    _module.__default.zero#canCall(_module._default.zero$A)
         || 8 != $FunctionContextHeight
       ==> true);

function _module.__default.zero#requires(Ty, LayerType) : bool;

// #requires axiom for _module.__default.zero
axiom (forall _module._default.zero$A: Ty, $ly: LayerType :: 
  { _module.__default.zero#requires(_module._default.zero$A, $ly) } 
  _module.__default.zero#requires(_module._default.zero$A, $ly) == true);

// definition axiom for _module.__default.zero (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module._default.zero$A: Ty, $ly: LayerType :: 
    { _module.__default.zero(_module._default.zero$A, $LS($ly)) } 
    _module.__default.zero#canCall(_module._default.zero$A)
         || 8 != $FunctionContextHeight
       ==> _module.__default.zero(_module._default.zero$A, $LS($ly)) == LitInt(0));

// definition axiom for _module.__default.zero for all literals (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module._default.zero$A: Ty, $ly: LayerType :: 
    {:weight 3} { _module.__default.zero(_module._default.zero$A, $LS($ly)) } 
    _module.__default.zero#canCall(_module._default.zero$A)
         || 8 != $FunctionContextHeight
       ==> _module.__default.zero(_module._default.zero$A, $LS($ly)) == LitInt(0));

procedure {:opaque} CheckWellformed$$_module.__default.zero(_module._default.zero$A: Ty);
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$_module.__default.reveal__id();
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel__module._default.id0: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$_module.__default.reveal__id();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel__module._default.id == $LS(MoreFuel__module._default.id0);
  free ensures StartFuelAssert__module._default.id == $LS($LS(MoreFuel__module._default.id0));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel__module._default.id0) == MoreFuel__module._default.id0;



procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$_module.__default.reveal__id__box();
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel__module._default.id_box0: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$_module.__default.reveal__id__box();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel__module._default.id_box == $LS(MoreFuel__module._default.id_box0);
  free ensures StartFuelAssert__module._default.id_box
     == $LS($LS(MoreFuel__module._default.id_box0));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel__module._default.id_box0)
     == MoreFuel__module._default.id_box0;



procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$_module.__default.reveal__zero();
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel__module._default.zero0: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$_module.__default.reveal__zero();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel__module._default.zero == $LS(MoreFuel__module._default.zero0);
  free ensures StartFuelAssert__module._default.zero
     == $LS($LS(MoreFuel__module._default.zero0));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel__module._default.zero0) == MoreFuel__module._default.zero0;



const unique class.A_k.C?: ClassName;

function Tclass.A_k.C?() : Ty;

const unique Tagclass.A_k.C?: TyTag;

// Tclass.A_k.C? Tag
axiom Tag(Tclass.A_k.C?()) == Tagclass.A_k.C?
   && TagFamily(Tclass.A_k.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.A_k.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A_k.C?()) } 
  $IsBox(bx, Tclass.A_k.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.A_k.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.A_k.C?()) } 
  $Is($o, Tclass.A_k.C?()) <==> $o == null || dtype($o) == Tclass.A_k.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.A_k.C?(), $h) } 
  $IsAlloc($o, Tclass.A_k.C?(), $h) <==> $o == null || read($h, $o, alloc));

// function declaration for A'.C.Valid
function A_k.C.Valid($heap: Heap, this: ref) : bool;

function A_k.C.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.A_k.C() : Ty;

const unique Tagclass.A_k.C: TyTag;

// Tclass.A_k.C Tag
axiom Tag(Tclass.A_k.C()) == Tagclass.A_k.C
   && TagFamily(Tclass.A_k.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.A_k.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.A_k.C()) } 
  $IsBox(bx, Tclass.A_k.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.A_k.C()));

// frame axiom for A_k.C.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), A_k.C.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.A_k.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> A_k.C.Valid($h0, this) == A_k.C.Valid($h1, this));

axiom FDim(A_k.C.x) == 0
   && FieldOfDecl(class.A_k.C?, field$x) == A_k.C.x
   && !$IsGhostField(A_k.C.x);

// consequence axiom for A_k.C.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { A_k.C.Valid($Heap, this) } 
    A_k.C.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.A_k.C())
           && $IsAlloc(this, Tclass.A_k.C(), $Heap))
       ==> (A_k.C.Valid($Heap, this) ==> LitInt(0) <= read($Heap, this, A_k.C.x))
         && (read($Heap, this, A_k.C.x) == LitInt(8) ==> A_k.C.Valid($Heap, this)));

function A_k.C.Valid#requires(Heap, ref) : bool;

// #requires axiom for A_k.C.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { A_k.C.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.A_k.C())
       && $IsAlloc(this, Tclass.A_k.C(), $Heap)
     ==> A_k.C.Valid#requires($Heap, this) == true);

// function declaration for A'.C.RevealedValid
function A_k.C.RevealedValid($heap: Heap, this: ref) : bool;

function A_k.C.RevealedValid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for A_k.C.RevealedValid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), A_k.C.RevealedValid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.A_k.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> A_k.C.RevealedValid($h0, this) == A_k.C.RevealedValid($h1, this));

// consequence axiom for A_k.C.RevealedValid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { A_k.C.RevealedValid($Heap, this) } 
    A_k.C.RevealedValid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.A_k.C())
           && $IsAlloc(this, Tclass.A_k.C(), $Heap))
       ==> (A_k.C.Valid($Heap, this) ==> LitInt(0) <= read($Heap, this, A_k.C.x))
         && (read($Heap, this, A_k.C.x) == LitInt(8) ==> A_k.C.Valid($Heap, this)));

function A_k.C.RevealedValid#requires(Heap, ref) : bool;

// #requires axiom for A_k.C.RevealedValid
axiom (forall $Heap: Heap, this: ref :: 
  { A_k.C.RevealedValid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.A_k.C())
       && $IsAlloc(this, Tclass.A_k.C(), $Heap)
     ==> A_k.C.RevealedValid#requires($Heap, this) == true);

// definition axiom for A_k.C.RevealedValid (revealed)
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { A_k.C.RevealedValid($Heap, this), $IsGoodHeap($Heap) } 
    A_k.C.RevealedValid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.A_k.C())
           && $IsAlloc(this, Tclass.A_k.C(), $Heap))
       ==> A_k.C.RevealedValid($Heap, this) == (read($Heap, this, A_k.C.x) == LitInt(8)));

const A_k.C.x: Field int;

// C.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, A_k.C.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.A_k.C?()
     ==> $Is(read($h, $o, A_k.C.x), TInt));

// C.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, A_k.C.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.A_k.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, A_k.C.x), TInt, $h));

// function declaration for A'.C.Get
function A_k.C.Get($heap: Heap, this: ref) : int;

function A_k.C.Get#canCall($heap: Heap, this: ref) : bool;

// frame axiom for A_k.C.Get
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), A_k.C.Get($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.A_k.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> A_k.C.Get($h0, this) == A_k.C.Get($h1, this));

// consequence axiom for A_k.C.Get
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { A_k.C.Get($Heap, this) } 
    A_k.C.Get#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.A_k.C())
           && $IsAlloc(this, Tclass.A_k.C(), $Heap))
       ==> true);

function A_k.C.Get#requires(Heap, ref) : bool;

// #requires axiom for A_k.C.Get
axiom (forall $Heap: Heap, this: ref :: 
  { A_k.C.Get#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.A_k.C())
       && $IsAlloc(this, Tclass.A_k.C(), $Heap)
     ==> A_k.C.Get#requires($Heap, this) == true);

// A'.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.A_k.C()) } 
  $Is(c#0, Tclass.A_k.C()) <==> $Is(c#0, Tclass.A_k.C?()) && c#0 != null);

// A'.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.A_k.C(), $h) } 
  $IsAlloc(c#0, Tclass.A_k.C(), $h) <==> $IsAlloc(c#0, Tclass.A_k.C?(), $h));

const #$_default: Ty;

const unique class.A_k.__default: ClassName;

function Tclass.A_k.__default() : Ty;

const unique Tagclass.A_k.__default: TyTag;

// Tclass.A_k.__default Tag
axiom Tag(Tclass.A_k.__default()) == Tagclass.A_k.__default
   && TagFamily(Tclass.A_k.__default()) == tytagFamily$_default;

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.A_k.__default()) } 
  $Is($o, Tclass.A_k.__default())
     <==> $o == null || dtype($o) == Tclass.A_k.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.A_k.__default(), $h) } 
  $IsAlloc($o, Tclass.A_k.__default(), $h) <==> $o == null || read($h, $o, alloc));

const unique class.B.__default: ClassName;

function Tclass.B.__default() : Ty;

const unique Tagclass.B.__default: TyTag;

// Tclass.B.__default Tag
axiom Tag(Tclass.B.__default()) == Tagclass.B.__default
   && TagFamily(Tclass.B.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.B.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B.__default()) } 
  $IsBox(bx, Tclass.B.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B.__default()) } 
  $Is($o, Tclass.B.__default())
     <==> $o == null || dtype($o) == Tclass.B.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B.__default(), $h) } 
  $IsAlloc($o, Tclass.B.__default(), $h) <==> $o == null || read($h, $o, alloc));

const unique class.B__direct.__default: ClassName;

function Tclass.B__direct.__default() : Ty;

const unique Tagclass.B__direct.__default: TyTag;

// Tclass.B__direct.__default Tag
axiom Tag(Tclass.B__direct.__default()) == Tagclass.B__direct.__default
   && TagFamily(Tclass.B__direct.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.B__direct.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B__direct.__default()) } 
  $IsBox(bx, Tclass.B__direct.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.B__direct.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B__direct.__default()) } 
  $Is($o, Tclass.B__direct.__default())
     <==> $o == null || dtype($o) == Tclass.B__direct.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B__direct.__default(), $h) } 
  $IsAlloc($o, Tclass.B__direct.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.B__more.__default: ClassName;

function Tclass.B__more.__default() : Ty;

const unique Tagclass.B__more.__default: TyTag;

// Tclass.B__more.__default Tag
axiom Tag(Tclass.B__more.__default()) == Tagclass.B__more.__default
   && TagFamily(Tclass.B__more.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.B__more.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B__more.__default()) } 
  $IsBox(bx, Tclass.B__more.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B__more.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B__more.__default()) } 
  $Is($o, Tclass.B__more.__default())
     <==> $o == null || dtype($o) == Tclass.B__more.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B__more.__default(), $h) } 
  $IsAlloc($o, Tclass.B__more.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const unique class.B_k.__default: ClassName;

function Tclass.B_k.__default() : Ty;

const unique Tagclass.B_k.__default: TyTag;

// Tclass.B_k.__default Tag
axiom Tag(Tclass.B_k.__default()) == Tagclass.B_k.__default
   && TagFamily(Tclass.B_k.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.B_k.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B_k.__default()) } 
  $IsBox(bx, Tclass.B_k.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B_k.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B_k.__default()) } 
  $Is($o, Tclass.B_k.__default())
     <==> $o == null || dtype($o) == Tclass.B_k.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B_k.__default(), $h) } 
  $IsAlloc($o, Tclass.B_k.__default(), $h) <==> $o == null || read($h, $o, alloc));

const unique class.OpaqueFunctionsAreNotInlined.__default: ClassName;

function Tclass.OpaqueFunctionsAreNotInlined.__default() : Ty;

const unique Tagclass.OpaqueFunctionsAreNotInlined.__default: TyTag;

// Tclass.OpaqueFunctionsAreNotInlined.__default Tag
axiom Tag(Tclass.OpaqueFunctionsAreNotInlined.__default())
     == Tagclass.OpaqueFunctionsAreNotInlined.__default
   && TagFamily(Tclass.OpaqueFunctionsAreNotInlined.__default())
     == tytagFamily$_default;

// Box/unbox axiom for Tclass.OpaqueFunctionsAreNotInlined.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.OpaqueFunctionsAreNotInlined.__default()) } 
  $IsBox(bx, Tclass.OpaqueFunctionsAreNotInlined.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.OpaqueFunctionsAreNotInlined.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.OpaqueFunctionsAreNotInlined.__default()) } 
  $Is($o, Tclass.OpaqueFunctionsAreNotInlined.__default())
     <==> $o == null || dtype($o) == Tclass.OpaqueFunctionsAreNotInlined.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.OpaqueFunctionsAreNotInlined.__default(), $h) } 
  $IsAlloc($o, Tclass.OpaqueFunctionsAreNotInlined.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for OpaqueFunctionsAreNotInlined._default.F
function OpaqueFunctionsAreNotInlined.__default.F($ly: LayerType, n#0: int) : bool;

function OpaqueFunctionsAreNotInlined.__default.F#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { OpaqueFunctionsAreNotInlined.__default.F($LS($ly), n#0) } 
  OpaqueFunctionsAreNotInlined.__default.F($LS($ly), n#0)
     == OpaqueFunctionsAreNotInlined.__default.F($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { OpaqueFunctionsAreNotInlined.__default.F(AsFuelBottom($ly), n#0) } 
  OpaqueFunctionsAreNotInlined.__default.F($ly, n#0)
     == OpaqueFunctionsAreNotInlined.__default.F($LZ, n#0));

// consequence axiom for OpaqueFunctionsAreNotInlined.__default.F
axiom true
   ==> (forall $ly: LayerType, n#0: int :: 
    { OpaqueFunctionsAreNotInlined.__default.F($ly, n#0) } 
    true ==> true);

function OpaqueFunctionsAreNotInlined.__default.F#requires(LayerType, int) : bool;

// #requires axiom for OpaqueFunctionsAreNotInlined.__default.F
axiom (forall $ly: LayerType, n#0: int :: 
  { OpaqueFunctionsAreNotInlined.__default.F#requires($ly, n#0) } 
  OpaqueFunctionsAreNotInlined.__default.F#requires($ly, n#0) == true);

// definition axiom for OpaqueFunctionsAreNotInlined.__default.F (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: int :: 
    { OpaqueFunctionsAreNotInlined.__default.F($LS($ly), n#0) } 
    true
       ==> OpaqueFunctionsAreNotInlined.__default.F($LS($ly), n#0)
         == (LitInt(0) <= n#0 && n#0 < 100));

// definition axiom for OpaqueFunctionsAreNotInlined.__default.F for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { OpaqueFunctionsAreNotInlined.__default.F($LS($ly), LitInt(n#0)) } 
    true
       ==> OpaqueFunctionsAreNotInlined.__default.F($LS($ly), LitInt(n#0))
         == (LitInt(0) <= LitInt(n#0) && n#0 < 100));

const unique class.M0.__default: ClassName;

function Tclass.M0.__default() : Ty;

const unique Tagclass.M0.__default: TyTag;

// Tclass.M0.__default Tag
axiom Tag(Tclass.M0.__default()) == Tagclass.M0.__default
   && TagFamily(Tclass.M0.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.M0.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M0.__default()) } 
  $IsBox(bx, Tclass.M0.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M0.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M0.__default()) } 
  $Is($o, Tclass.M0.__default())
     <==> $o == null || dtype($o) == Tclass.M0.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M0.__default(), $h) } 
  $IsAlloc($o, Tclass.M0.__default(), $h) <==> $o == null || read($h, $o, alloc));

// function declaration for M0._default.F
function M0.__default.F($ly: LayerType) : int;

function M0.__default.F#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { M0.__default.F($LS($ly)) } 
  M0.__default.F($LS($ly)) == M0.__default.F($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { M0.__default.F(AsFuelBottom($ly)) } 
  M0.__default.F($ly) == M0.__default.F($LZ));

// consequence axiom for M0.__default.F
axiom true ==> (forall $ly: LayerType :: { M0.__default.F($ly) } true ==> true);

function M0.__default.F#requires(LayerType) : bool;

// #requires axiom for M0.__default.F
axiom (forall $ly: LayerType :: 
  { M0.__default.F#requires($ly) } 
  M0.__default.F#requires($ly) == true);

// definition axiom for M0.__default.F (revealed)
axiom true
   ==> (forall $ly: LayerType :: 
    { M0.__default.F($LS($ly)) } 
    true ==> M0.__default.F($LS($ly)) == LitInt(12));

// definition axiom for M0.__default.F for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType :: 
    {:weight 3} { M0.__default.F($LS($ly)) } 
    true ==> M0.__default.F($LS($ly)) == LitInt(12));

const unique class.M1.__default: ClassName;

function Tclass.M1.__default() : Ty;

const unique Tagclass.M1.__default: TyTag;

// Tclass.M1.__default Tag
axiom Tag(Tclass.M1.__default()) == Tagclass.M1.__default
   && TagFamily(Tclass.M1.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.M1.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.M1.__default()) } 
  $IsBox(bx, Tclass.M1.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.M1.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.M1.__default()) } 
  $Is($o, Tclass.M1.__default())
     <==> $o == null || dtype($o) == Tclass.M1.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.M1.__default(), $h) } 
  $IsAlloc($o, Tclass.M1.__default(), $h) <==> $o == null || read($h, $o, alloc));

// function declaration for M1._default.F
function M1.__default.F($ly: LayerType) : int;

function M1.__default.F#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { M1.__default.F($LS($ly)) } 
  M1.__default.F($LS($ly)) == M1.__default.F($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { M1.__default.F(AsFuelBottom($ly)) } 
  M1.__default.F($ly) == M1.__default.F($LZ));

// consequence axiom for M1.__default.F
axiom true ==> (forall $ly: LayerType :: { M1.__default.F($ly) } true ==> true);

function M1.__default.F#requires(LayerType) : bool;

// #requires axiom for M1.__default.F
axiom (forall $ly: LayerType :: 
  { M1.__default.F#requires($ly) } 
  M1.__default.F#requires($ly) == true);

// definition axiom for M1.__default.F (revealed)
axiom true
   ==> (forall $ly: LayerType :: 
    { M1.__default.F($LS($ly)) } 
    true ==> M1.__default.F($LS($ly)) == LitInt(12));

// definition axiom for M1.__default.F for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType :: 
    {:weight 3} { M1.__default.F($LS($ly)) } 
    true ==> M1.__default.F($LS($ly)) == LitInt(12));

const unique class.LayerQuantifiers.__default: ClassName;

function Tclass.LayerQuantifiers.__default() : Ty;

const unique Tagclass.LayerQuantifiers.__default: TyTag;

// Tclass.LayerQuantifiers.__default Tag
axiom Tag(Tclass.LayerQuantifiers.__default()) == Tagclass.LayerQuantifiers.__default
   && TagFamily(Tclass.LayerQuantifiers.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.LayerQuantifiers.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.LayerQuantifiers.__default()) } 
  $IsBox(bx, Tclass.LayerQuantifiers.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.LayerQuantifiers.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.LayerQuantifiers.__default()) } 
  $Is($o, Tclass.LayerQuantifiers.__default())
     <==> $o == null || dtype($o) == Tclass.LayerQuantifiers.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.LayerQuantifiers.__default(), $h) } 
  $IsAlloc($o, Tclass.LayerQuantifiers.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for LayerQuantifiers._default.f
function LayerQuantifiers.__default.f($ly: LayerType, x#0: int) : bool;

function LayerQuantifiers.__default.f#canCall(x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { LayerQuantifiers.__default.f($LS($ly), x#0) } 
  LayerQuantifiers.__default.f($LS($ly), x#0)
     == LayerQuantifiers.__default.f($ly, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { LayerQuantifiers.__default.f(AsFuelBottom($ly), x#0) } 
  LayerQuantifiers.__default.f($ly, x#0) == LayerQuantifiers.__default.f($LZ, x#0));

// consequence axiom for LayerQuantifiers.__default.f
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { LayerQuantifiers.__default.f($ly, x#0) } 
    LayerQuantifiers.__default.f#canCall(x#0) || LitInt(0) <= x#0 ==> true);

function LayerQuantifiers.__default.f#requires(LayerType, int) : bool;

// #requires axiom for LayerQuantifiers.__default.f
axiom (forall $ly: LayerType, x#0: int :: 
  { LayerQuantifiers.__default.f#requires($ly, x#0) } 
  LitInt(0) <= x#0 ==> LayerQuantifiers.__default.f#requires($ly, x#0) == true);

// definition axiom for LayerQuantifiers.__default.f (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { LayerQuantifiers.__default.f($LS($ly), x#0) } 
    LayerQuantifiers.__default.f#canCall(x#0) || LitInt(0) <= x#0
       ==> (x#0 != LitInt(0) ==> LayerQuantifiers.__default.f#canCall(x#0 - 1))
         && LayerQuantifiers.__default.f($LS($ly), x#0)
           == (if x#0 == LitInt(0) then true else LayerQuantifiers.__default.f($ly, x#0 - 1)));

// definition axiom for LayerQuantifiers.__default.f for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    {:weight 3} { LayerQuantifiers.__default.f($LS($ly), LitInt(x#0)) } 
    LayerQuantifiers.__default.f#canCall(LitInt(x#0)) || LitInt(0) <= x#0
       ==> (LitInt(x#0) != LitInt(0)
           ==> LayerQuantifiers.__default.f#canCall(LitInt(x#0 - 1)))
         && LayerQuantifiers.__default.f($LS($ly), LitInt(x#0))
           == (if LitInt(x#0) == LitInt(0)
             then true
             else LayerQuantifiers.__default.f($LS($ly), LitInt(x#0 - 1))));

// Constructor function declaration
function #Regression.List.Nil() : DatatypeType;

const unique ##Regression.List.Nil: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#Regression.List.Nil()) == ##Regression.List.Nil;

function Regression.List.Nil_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { Regression.List.Nil_q(d) } 
  Regression.List.Nil_q(d) <==> DatatypeCtorId(d) == ##Regression.List.Nil);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { Regression.List.Nil_q(d) } 
  Regression.List.Nil_q(d) ==> d == #Regression.List.Nil());

function Tclass.Regression.List(Ty) : Ty;

const unique Tagclass.Regression.List: TyTag;

// Tclass.Regression.List Tag
axiom (forall Regression.List$A: Ty :: 
  { Tclass.Regression.List(Regression.List$A) } 
  Tag(Tclass.Regression.List(Regression.List$A)) == Tagclass.Regression.List
     && TagFamily(Tclass.Regression.List(Regression.List$A)) == tytagFamily$List);

// Tclass.Regression.List injectivity 0
axiom (forall Regression.List$A: Ty :: 
  { Tclass.Regression.List(Regression.List$A) } 
  Tclass.Regression.List_0(Tclass.Regression.List(Regression.List$A))
     == Regression.List$A);

function Tclass.Regression.List_0(Ty) : Ty;

// Box/unbox axiom for Tclass.Regression.List
axiom (forall Regression.List$A: Ty, bx: Box :: 
  { $IsBox(bx, Tclass.Regression.List(Regression.List$A)) } 
  $IsBox(bx, Tclass.Regression.List(Regression.List$A))
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.Regression.List(Regression.List$A)));

// Constructor $Is
axiom (forall Regression.List$A: Ty :: 
  { $Is(#Regression.List.Nil(), Tclass.Regression.List(Regression.List$A)) } 
  $Is(#Regression.List.Nil(), Tclass.Regression.List(Regression.List$A)));

// Constructor $IsAlloc
axiom (forall Regression.List$A: Ty, $h: Heap :: 
  { $IsAlloc(#Regression.List.Nil(), Tclass.Regression.List(Regression.List$A), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#Regression.List.Nil(), Tclass.Regression.List(Regression.List$A), $h));

// Constructor literal
axiom #Regression.List.Nil() == Lit(#Regression.List.Nil());

// Constructor function declaration
function #Regression.List.Cons(Box, DatatypeType) : DatatypeType;

const unique ##Regression.List.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: Box, a#5#1#0: DatatypeType :: 
  { #Regression.List.Cons(a#5#0#0, a#5#1#0) } 
  DatatypeCtorId(#Regression.List.Cons(a#5#0#0, a#5#1#0))
     == ##Regression.List.Cons);

function Regression.List.Cons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { Regression.List.Cons_q(d) } 
  Regression.List.Cons_q(d) <==> DatatypeCtorId(d) == ##Regression.List.Cons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { Regression.List.Cons_q(d) } 
  Regression.List.Cons_q(d)
     ==> (exists a#6#0#0: Box, a#6#1#0: DatatypeType :: 
      d == #Regression.List.Cons(a#6#0#0, a#6#1#0)));

// Constructor $Is
axiom (forall Regression.List$A: Ty, a#7#0#0: Box, a#7#1#0: DatatypeType :: 
  { $Is(#Regression.List.Cons(a#7#0#0, a#7#1#0), 
      Tclass.Regression.List(Regression.List$A)) } 
  $Is(#Regression.List.Cons(a#7#0#0, a#7#1#0), 
      Tclass.Regression.List(Regression.List$A))
     <==> $IsBox(a#7#0#0, Regression.List$A)
       && $Is(a#7#1#0, Tclass.Regression.List(Regression.List$A)));

// Constructor $IsAlloc
axiom (forall Regression.List$A: Ty, a#8#0#0: Box, a#8#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#Regression.List.Cons(a#8#0#0, a#8#1#0), 
      Tclass.Regression.List(Regression.List$A), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#Regression.List.Cons(a#8#0#0, a#8#1#0), 
        Tclass.Regression.List(Regression.List$A), 
        $h)
       <==> $IsAllocBox(a#8#0#0, Regression.List$A, $h)
         && $IsAlloc(a#8#1#0, Tclass.Regression.List(Regression.List$A), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, Regression.List$A: Ty, $h: Heap :: 
  { $IsAllocBox(Regression.List._h1(d), Regression.List$A, $h) } 
  $IsGoodHeap($h)
       && 
      Regression.List.Cons_q(d)
       && $IsAlloc(d, Tclass.Regression.List(Regression.List$A), $h)
     ==> $IsAllocBox(Regression.List._h1(d), Regression.List$A, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, Regression.List$A: Ty, $h: Heap :: 
  { $IsAlloc(Regression.List.tl(d), Tclass.Regression.List(Regression.List$A), $h) } 
  $IsGoodHeap($h)
       && 
      Regression.List.Cons_q(d)
       && $IsAlloc(d, Tclass.Regression.List(Regression.List$A), $h)
     ==> $IsAlloc(Regression.List.tl(d), Tclass.Regression.List(Regression.List$A), $h));

// Constructor literal
axiom (forall a#9#0#0: Box, a#9#1#0: DatatypeType :: 
  { #Regression.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0)) } 
  #Regression.List.Cons(Lit(a#9#0#0), Lit(a#9#1#0))
     == Lit(#Regression.List.Cons(a#9#0#0, a#9#1#0)));

function Regression.List._h1(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#10#0#0: Box, a#10#1#0: DatatypeType :: 
  { #Regression.List.Cons(a#10#0#0, a#10#1#0) } 
  Regression.List._h1(#Regression.List.Cons(a#10#0#0, a#10#1#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: Box, a#11#1#0: DatatypeType :: 
  { #Regression.List.Cons(a#11#0#0, a#11#1#0) } 
  BoxRank(a#11#0#0) < DtRank(#Regression.List.Cons(a#11#0#0, a#11#1#0)));

function Regression.List.tl(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#12#0#0: Box, a#12#1#0: DatatypeType :: 
  { #Regression.List.Cons(a#12#0#0, a#12#1#0) } 
  Regression.List.tl(#Regression.List.Cons(a#12#0#0, a#12#1#0)) == a#12#1#0);

// Inductive rank
axiom (forall a#13#0#0: Box, a#13#1#0: DatatypeType :: 
  { #Regression.List.Cons(a#13#0#0, a#13#1#0) } 
  DtRank(a#13#1#0) < DtRank(#Regression.List.Cons(a#13#0#0, a#13#1#0)));

// Depth-one case-split function
function $IsA#Regression.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#Regression.List(d) } 
  $IsA#Regression.List(d)
     ==> Regression.List.Nil_q(d) || Regression.List.Cons_q(d));

// Questionmark data type disjunctivity
axiom (forall Regression.List$A: Ty, d: DatatypeType :: 
  { Regression.List.Cons_q(d), $Is(d, Tclass.Regression.List(Regression.List$A)) } 
    { Regression.List.Nil_q(d), $Is(d, Tclass.Regression.List(Regression.List$A)) } 
  $Is(d, Tclass.Regression.List(Regression.List$A))
     ==> Regression.List.Nil_q(d) || Regression.List.Cons_q(d));

// Datatype extensional equality declaration
function Regression.List#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #Regression.List.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Regression.List#Equal(a, b), Regression.List.Nil_q(a) } 
    { Regression.List#Equal(a, b), Regression.List.Nil_q(b) } 
  Regression.List.Nil_q(a) && Regression.List.Nil_q(b)
     ==> (Regression.List#Equal(a, b) <==> true));

// Datatype extensional equality definition: #Regression.List.Cons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Regression.List#Equal(a, b), Regression.List.Cons_q(a) } 
    { Regression.List#Equal(a, b), Regression.List.Cons_q(b) } 
  Regression.List.Cons_q(a) && Regression.List.Cons_q(b)
     ==> (Regression.List#Equal(a, b)
       <==> Regression.List._h1(a) == Regression.List._h1(b)
         && Regression.List#Equal(Regression.List.tl(a), Regression.List.tl(b))));

// Datatype extensionality axiom: Regression.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { Regression.List#Equal(a, b) } 
  Regression.List#Equal(a, b) <==> a == b);

const unique class.Regression.List: ClassName;

const unique class.Regression.__default: ClassName;

function Tclass.Regression.__default() : Ty;

const unique Tagclass.Regression.__default: TyTag;

// Tclass.Regression.__default Tag
axiom Tag(Tclass.Regression.__default()) == Tagclass.Regression.__default
   && TagFamily(Tclass.Regression.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.Regression.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.Regression.__default()) } 
  $IsBox(bx, Tclass.Regression.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.Regression.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.Regression.__default()) } 
  $Is($o, Tclass.Regression.__default())
     <==> $o == null || dtype($o) == Tclass.Regression.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.Regression.__default(), $h) } 
  $IsAlloc($o, Tclass.Regression.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for Regression._default.Empty
function Regression.__default.Empty(Regression._default.Empty$A: Ty) : DatatypeType;

function Regression.__default.Empty#canCall(Regression._default.Empty$A: Ty) : bool;

// consequence axiom for Regression.__default.Empty
axiom true
   ==> (forall Regression._default.Empty$A: Ty :: 
    { Regression.__default.Empty(Regression._default.Empty$A) } 
    true
       ==> $Is(Regression.__default.Empty(Regression._default.Empty$A), 
        Tclass.Regression.List(Regression._default.Empty$A)));

function Regression.__default.Empty#requires(Ty) : bool;

// #requires axiom for Regression.__default.Empty
axiom (forall Regression._default.Empty$A: Ty :: 
  { Regression.__default.Empty#requires(Regression._default.Empty$A) } 
  Regression.__default.Empty#requires(Regression._default.Empty$A) == true);

// definition axiom for Regression.__default.Empty (revealed)
axiom true
   ==> (forall Regression._default.Empty$A: Ty :: 
    { Regression.__default.Empty(Regression._default.Empty$A) } 
    true
       ==> Regression.__default.Empty(Regression._default.Empty$A)
         == Lit(#Regression.List.Nil()));

// definition axiom for Regression.__default.Empty for all literals (revealed)
axiom true
   ==> (forall Regression._default.Empty$A: Ty :: 
    {:weight 3} { Regression.__default.Empty(Regression._default.Empty$A) } 
    true
       ==> Regression.__default.Empty(Regression._default.Empty$A)
         == Lit(#Regression.List.Nil()));

// function declaration for Regression._default.Length
function Regression.__default.Length(Regression._default.Length$A: Ty, $ly: LayerType, s#0: DatatypeType) : int;

function Regression.__default.Length#canCall(Regression._default.Length$A: Ty, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall Regression._default.Length$A: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { Regression.__default.Length(Regression._default.Length$A, $LS($ly), s#0) } 
  Regression.__default.Length(Regression._default.Length$A, $LS($ly), s#0)
     == Regression.__default.Length(Regression._default.Length$A, $ly, s#0));

// fuel synonym axiom
axiom (forall Regression._default.Length$A: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { Regression.__default.Length(Regression._default.Length$A, AsFuelBottom($ly), s#0) } 
  Regression.__default.Length(Regression._default.Length$A, $ly, s#0)
     == Regression.__default.Length(Regression._default.Length$A, $LZ, s#0));

// consequence axiom for Regression.__default.Length
axiom true
   ==> (forall Regression._default.Length$A: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { Regression.__default.Length(Regression._default.Length$A, $ly, s#0) } 
    Regression.__default.Length#canCall(Regression._default.Length$A, s#0)
         || $Is(s#0, Tclass.Regression.List(Regression._default.Length$A))
       ==> LitInt(0) <= Regression.__default.Length(Regression._default.Length$A, $ly, s#0));

function Regression.__default.Length#requires(Ty, LayerType, DatatypeType) : bool;

// #requires axiom for Regression.__default.Length
axiom (forall Regression._default.Length$A: Ty, $ly: LayerType, s#0: DatatypeType :: 
  { Regression.__default.Length#requires(Regression._default.Length$A, $ly, s#0) } 
  $Is(s#0, Tclass.Regression.List(Regression._default.Length$A))
     ==> Regression.__default.Length#requires(Regression._default.Length$A, $ly, s#0)
       == true);

// definition axiom for Regression.__default.Length (revealed)
axiom true
   ==> (forall Regression._default.Length$A: Ty, $ly: LayerType, s#0: DatatypeType :: 
    { Regression.__default.Length(Regression._default.Length$A, $LS($ly), s#0) } 
    Regression.__default.Length#canCall(Regression._default.Length$A, s#0)
         || $Is(s#0, Tclass.Regression.List(Regression._default.Length$A))
       ==> (Regression.List.Cons_q(s#0)
           ==> Regression.__default.Length#canCall(Regression._default.Length$A, Regression.List.tl(s#0)))
         && Regression.__default.Length(Regression._default.Length$A, $LS($ly), s#0)
           == (if Regression.List.Cons_q(s#0)
             then 1
               + Regression.__default.Length(Regression._default.Length$A, $ly, Regression.List.tl(s#0))
             else 0));

// definition axiom for Regression.__default.Length for all literals (revealed)
axiom true
   ==> (forall Regression._default.Length$A: Ty, $ly: LayerType, s#0: DatatypeType :: 
    {:weight 3} { Regression.__default.Length(Regression._default.Length$A, $LS($ly), Lit(s#0)) } 
    Regression.__default.Length#canCall(Regression._default.Length$A, Lit(s#0))
         || $Is(s#0, Tclass.Regression.List(Regression._default.Length$A))
       ==> (Lit(Regression.List.Cons_q(Lit(s#0)))
           ==> Regression.__default.Length#canCall(Regression._default.Length$A, Lit(Regression.List.tl(Lit(s#0)))))
         && Regression.__default.Length(Regression._default.Length$A, $LS($ly), Lit(s#0))
           == (if Regression.List.Cons_q(Lit(s#0))
             then 1
               + Regression.__default.Length(Regression._default.Length$A, $LS($ly), Lit(Regression.List.tl(Lit(s#0))))
             else 0));

const unique class.TypeMembers.Tr?: ClassName;

function Tclass.TypeMembers.Tr?() : Ty;

const unique Tagclass.TypeMembers.Tr?: TyTag;

// Tclass.TypeMembers.Tr? Tag
axiom Tag(Tclass.TypeMembers.Tr?()) == Tagclass.TypeMembers.Tr?
   && TagFamily(Tclass.TypeMembers.Tr?()) == tytagFamily$Tr;

// Box/unbox axiom for Tclass.TypeMembers.Tr?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TypeMembers.Tr?()) } 
  $IsBox(bx, Tclass.TypeMembers.Tr?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.TypeMembers.Tr?()));

// Tr: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TypeMembers.Tr?()) } 
  $Is($o, Tclass.TypeMembers.Tr?())
     <==> $o == null || implements$TypeMembers.Tr(dtype($o)));

// Tr: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TypeMembers.Tr?(), $h) } 
  $IsAlloc($o, Tclass.TypeMembers.Tr?(), $h)
     <==> $o == null || read($h, $o, alloc));

function implements$TypeMembers.Tr(Ty) : bool;

function TypeMembers.Tr.fav(this: ref) : bool;

// Tr.fav: Type axiom
axiom (forall $o: ref :: 
  { TypeMembers.Tr.fav($o) } 
  $Is(TypeMembers.Tr.fav($o), TBool));

// Tr.fav: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { TypeMembers.Tr.fav($o), read($h, $o, alloc) } 
  $IsGoodHeap($h) && read($h, $o, alloc)
     ==> $IsAlloc(TypeMembers.Tr.fav($o), TBool, $h));

// function declaration for TypeMembers.Tr.IsFavorite
function TypeMembers.Tr.IsFavorite($ly: LayerType, this: ref) : bool;

function TypeMembers.Tr.IsFavorite#canCall(this: ref) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: ref :: 
  { TypeMembers.Tr.IsFavorite($LS($ly), this) } 
  TypeMembers.Tr.IsFavorite($LS($ly), this)
     == TypeMembers.Tr.IsFavorite($ly, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: ref :: 
  { TypeMembers.Tr.IsFavorite(AsFuelBottom($ly), this) } 
  TypeMembers.Tr.IsFavorite($ly, this) == TypeMembers.Tr.IsFavorite($LZ, this));

function Tclass.TypeMembers.Tr() : Ty;

const unique Tagclass.TypeMembers.Tr: TyTag;

// Tclass.TypeMembers.Tr Tag
axiom Tag(Tclass.TypeMembers.Tr()) == Tagclass.TypeMembers.Tr
   && TagFamily(Tclass.TypeMembers.Tr()) == tytagFamily$Tr;

// Box/unbox axiom for Tclass.TypeMembers.Tr
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TypeMembers.Tr()) } 
  $IsBox(bx, Tclass.TypeMembers.Tr())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.TypeMembers.Tr()));

// consequence axiom for TypeMembers.Tr.IsFavorite
axiom true
   ==> (forall $ly: LayerType, this: ref :: 
    { TypeMembers.Tr.IsFavorite($ly, this) } 
    TypeMembers.Tr.IsFavorite#canCall(this)
         || (this != null && $Is(this, Tclass.TypeMembers.Tr()))
       ==> true);

function TypeMembers.Tr.IsFavorite#requires(LayerType, ref) : bool;

// #requires axiom for TypeMembers.Tr.IsFavorite
axiom (forall $ly: LayerType, $Heap: Heap, this: ref :: 
  { TypeMembers.Tr.IsFavorite#requires($ly, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.TypeMembers.Tr())
       && $IsAlloc(this, Tclass.TypeMembers.Tr(), $Heap)
     ==> TypeMembers.Tr.IsFavorite#requires($ly, this) == true);

// definition axiom for TypeMembers.Tr.IsFavorite (revealed)
axiom true
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    { TypeMembers.Tr.IsFavorite($LS($ly), this), $IsGoodHeap($Heap) } 
    TypeMembers.Tr.IsFavorite#canCall(this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.TypeMembers.Tr())
           && $IsAlloc(this, Tclass.TypeMembers.Tr(), $Heap))
       ==> TypeMembers.Tr.IsFavorite($LS($ly), this) == TypeMembers.Tr.fav(this));

// definition axiom for TypeMembers.Tr.IsFavorite for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, $Heap: Heap, this: ref :: 
    {:weight 3} { TypeMembers.Tr.IsFavorite($LS($ly), Lit(this)), $IsGoodHeap($Heap) } 
    TypeMembers.Tr.IsFavorite#canCall(Lit(this))
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.TypeMembers.Tr())
           && $IsAlloc(this, Tclass.TypeMembers.Tr(), $Heap))
       ==> TypeMembers.Tr.IsFavorite($LS($ly), Lit(this)) == TypeMembers.Tr.fav(Lit(this)));

// function declaration for TypeMembers.Tr.IsFive
function TypeMembers.Tr.IsFive($ly: LayerType, x#0: int) : bool;

function TypeMembers.Tr.IsFive#canCall(x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Tr.IsFive($LS($ly), x#0) } 
  TypeMembers.Tr.IsFive($LS($ly), x#0) == TypeMembers.Tr.IsFive($ly, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Tr.IsFive(AsFuelBottom($ly), x#0) } 
  TypeMembers.Tr.IsFive($ly, x#0) == TypeMembers.Tr.IsFive($LZ, x#0));

// consequence axiom for TypeMembers.Tr.IsFive
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { TypeMembers.Tr.IsFive($ly, x#0) } 
    true ==> true);

function TypeMembers.Tr.IsFive#requires(LayerType, int) : bool;

// #requires axiom for TypeMembers.Tr.IsFive
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Tr.IsFive#requires($ly, x#0) } 
  TypeMembers.Tr.IsFive#requires($ly, x#0) == true);

// definition axiom for TypeMembers.Tr.IsFive (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { TypeMembers.Tr.IsFive($LS($ly), x#0) } 
    true ==> TypeMembers.Tr.IsFive($LS($ly), x#0) == (x#0 == LitInt(5)));

// definition axiom for TypeMembers.Tr.IsFive for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    {:weight 3} { TypeMembers.Tr.IsFive($LS($ly), LitInt(x#0)) } 
    true
       ==> TypeMembers.Tr.IsFive($LS($ly), LitInt(x#0)) == (LitInt(x#0) == LitInt(5)));

// TypeMembers.Tr: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.TypeMembers.Tr()) } 
  $Is(c#0, Tclass.TypeMembers.Tr())
     <==> $Is(c#0, Tclass.TypeMembers.Tr?()) && c#0 != null);

// TypeMembers.Tr: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.TypeMembers.Tr(), $h) } 
  $IsAlloc(c#0, Tclass.TypeMembers.Tr(), $h)
     <==> $IsAlloc(c#0, Tclass.TypeMembers.Tr?(), $h));

// Constructor function declaration
function #TypeMembers.Color.Carrot() : DatatypeType;

const unique ##TypeMembers.Color.Carrot: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#TypeMembers.Color.Carrot()) == ##TypeMembers.Color.Carrot;

function TypeMembers.Color.Carrot_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TypeMembers.Color.Carrot_q(d) } 
  TypeMembers.Color.Carrot_q(d)
     <==> DatatypeCtorId(d) == ##TypeMembers.Color.Carrot);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TypeMembers.Color.Carrot_q(d) } 
  TypeMembers.Color.Carrot_q(d) ==> d == #TypeMembers.Color.Carrot());

function Tclass.TypeMembers.Color() : Ty;

const unique Tagclass.TypeMembers.Color: TyTag;

// Tclass.TypeMembers.Color Tag
axiom Tag(Tclass.TypeMembers.Color()) == Tagclass.TypeMembers.Color
   && TagFamily(Tclass.TypeMembers.Color()) == tytagFamily$Color;

// Box/unbox axiom for Tclass.TypeMembers.Color
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TypeMembers.Color()) } 
  $IsBox(bx, Tclass.TypeMembers.Color())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.TypeMembers.Color()));

// Constructor $Is
axiom $Is(#TypeMembers.Color.Carrot(), Tclass.TypeMembers.Color());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#TypeMembers.Color.Carrot(), Tclass.TypeMembers.Color(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#TypeMembers.Color.Carrot(), Tclass.TypeMembers.Color(), $h));

// Constructor literal
axiom #TypeMembers.Color.Carrot() == Lit(#TypeMembers.Color.Carrot());

// Constructor function declaration
function #TypeMembers.Color.Pumpkin() : DatatypeType;

const unique ##TypeMembers.Color.Pumpkin: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#TypeMembers.Color.Pumpkin()) == ##TypeMembers.Color.Pumpkin;

function TypeMembers.Color.Pumpkin_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TypeMembers.Color.Pumpkin_q(d) } 
  TypeMembers.Color.Pumpkin_q(d)
     <==> DatatypeCtorId(d) == ##TypeMembers.Color.Pumpkin);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TypeMembers.Color.Pumpkin_q(d) } 
  TypeMembers.Color.Pumpkin_q(d) ==> d == #TypeMembers.Color.Pumpkin());

// Constructor $Is
axiom $Is(#TypeMembers.Color.Pumpkin(), Tclass.TypeMembers.Color());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#TypeMembers.Color.Pumpkin(), Tclass.TypeMembers.Color(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#TypeMembers.Color.Pumpkin(), Tclass.TypeMembers.Color(), $h));

// Constructor literal
axiom #TypeMembers.Color.Pumpkin() == Lit(#TypeMembers.Color.Pumpkin());

// Depth-one case-split function
function $IsA#TypeMembers.Color(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#TypeMembers.Color(d) } 
  $IsA#TypeMembers.Color(d)
     ==> TypeMembers.Color.Carrot_q(d) || TypeMembers.Color.Pumpkin_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { TypeMembers.Color.Pumpkin_q(d), $Is(d, Tclass.TypeMembers.Color()) } 
    { TypeMembers.Color.Carrot_q(d), $Is(d, Tclass.TypeMembers.Color()) } 
  $Is(d, Tclass.TypeMembers.Color())
     ==> TypeMembers.Color.Carrot_q(d) || TypeMembers.Color.Pumpkin_q(d));

// Datatype extensional equality declaration
function TypeMembers.Color#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #TypeMembers.Color.Carrot
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TypeMembers.Color#Equal(a, b), TypeMembers.Color.Carrot_q(a) } 
    { TypeMembers.Color#Equal(a, b), TypeMembers.Color.Carrot_q(b) } 
  TypeMembers.Color.Carrot_q(a) && TypeMembers.Color.Carrot_q(b)
     ==> (TypeMembers.Color#Equal(a, b) <==> true));

// Datatype extensional equality definition: #TypeMembers.Color.Pumpkin
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TypeMembers.Color#Equal(a, b), TypeMembers.Color.Pumpkin_q(a) } 
    { TypeMembers.Color#Equal(a, b), TypeMembers.Color.Pumpkin_q(b) } 
  TypeMembers.Color.Pumpkin_q(a) && TypeMembers.Color.Pumpkin_q(b)
     ==> (TypeMembers.Color#Equal(a, b) <==> true));

// Datatype extensionality axiom: TypeMembers.Color
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TypeMembers.Color#Equal(a, b) } 
  TypeMembers.Color#Equal(a, b) <==> a == b);

const unique class.TypeMembers.Color: ClassName;

// function declaration for TypeMembers.Color.IsFavorite
function TypeMembers.Color.IsFavorite($ly: LayerType, this: DatatypeType) : bool;

function TypeMembers.Color.IsFavorite#canCall(this: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: DatatypeType :: 
  { TypeMembers.Color.IsFavorite($LS($ly), this) } 
  TypeMembers.Color.IsFavorite($LS($ly), this)
     == TypeMembers.Color.IsFavorite($ly, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: DatatypeType :: 
  { TypeMembers.Color.IsFavorite(AsFuelBottom($ly), this) } 
  TypeMembers.Color.IsFavorite($ly, this)
     == TypeMembers.Color.IsFavorite($LZ, this));

// consequence axiom for TypeMembers.Color.IsFavorite
axiom true
   ==> (forall $ly: LayerType, this: DatatypeType :: 
    { TypeMembers.Color.IsFavorite($ly, this) } 
    TypeMembers.Color.IsFavorite#canCall(this)
         || $Is(this, Tclass.TypeMembers.Color())
       ==> true);

function TypeMembers.Color.IsFavorite#requires(LayerType, DatatypeType) : bool;

// #requires axiom for TypeMembers.Color.IsFavorite
axiom (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
  { TypeMembers.Color.IsFavorite#requires($ly, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      $Is(this, Tclass.TypeMembers.Color())
       && $IsAlloc(this, Tclass.TypeMembers.Color(), $Heap)
     ==> TypeMembers.Color.IsFavorite#requires($ly, this) == true);

// definition axiom for TypeMembers.Color.IsFavorite (revealed)
axiom true
   ==> (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
    { TypeMembers.Color.IsFavorite($LS($ly), this), $IsGoodHeap($Heap) } 
    TypeMembers.Color.IsFavorite#canCall(this)
         || ($IsGoodHeap($Heap)
           && 
          $Is(this, Tclass.TypeMembers.Color())
           && $IsAlloc(this, Tclass.TypeMembers.Color(), $Heap))
       ==> $IsA#TypeMembers.Color(this)
         && TypeMembers.Color.IsFavorite($LS($ly), this)
           == TypeMembers.Color#Equal(this, #TypeMembers.Color.Pumpkin()));

// definition axiom for TypeMembers.Color.IsFavorite for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, $Heap: Heap, this: DatatypeType :: 
    {:weight 3} { TypeMembers.Color.IsFavorite($LS($ly), Lit(this)), $IsGoodHeap($Heap) } 
    TypeMembers.Color.IsFavorite#canCall(Lit(this))
         || ($IsGoodHeap($Heap)
           && 
          $Is(this, Tclass.TypeMembers.Color())
           && $IsAlloc(this, Tclass.TypeMembers.Color(), $Heap))
       ==> $IsA#TypeMembers.Color(Lit(this))
         && TypeMembers.Color.IsFavorite($LS($ly), Lit(this))
           == TypeMembers.Color#Equal(this, #TypeMembers.Color.Pumpkin()));

// function declaration for TypeMembers.Color.IsFive
function TypeMembers.Color.IsFive($ly: LayerType, x#0: int) : bool;

function TypeMembers.Color.IsFive#canCall(x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Color.IsFive($LS($ly), x#0) } 
  TypeMembers.Color.IsFive($LS($ly), x#0) == TypeMembers.Color.IsFive($ly, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Color.IsFive(AsFuelBottom($ly), x#0) } 
  TypeMembers.Color.IsFive($ly, x#0) == TypeMembers.Color.IsFive($LZ, x#0));

// consequence axiom for TypeMembers.Color.IsFive
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { TypeMembers.Color.IsFive($ly, x#0) } 
    true ==> true);

function TypeMembers.Color.IsFive#requires(LayerType, int) : bool;

// #requires axiom for TypeMembers.Color.IsFive
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Color.IsFive#requires($ly, x#0) } 
  TypeMembers.Color.IsFive#requires($ly, x#0) == true);

// definition axiom for TypeMembers.Color.IsFive (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { TypeMembers.Color.IsFive($LS($ly), x#0) } 
    true ==> TypeMembers.Color.IsFive($LS($ly), x#0) == (x#0 == LitInt(5)));

// definition axiom for TypeMembers.Color.IsFive for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    {:weight 3} { TypeMembers.Color.IsFive($LS($ly), LitInt(x#0)) } 
    true
       ==> TypeMembers.Color.IsFive($LS($ly), LitInt(x#0)) == (LitInt(x#0) == LitInt(5)));

procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$TypeMembers.Color.reveal__IsFavorite(this: DatatypeType
       where $Is(this, Tclass.TypeMembers.Color())
         && $IsAlloc(this, Tclass.TypeMembers.Color(), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel_TypeMembers.Color.IsFavorite1: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$TypeMembers.Color.reveal__IsFavorite(this: DatatypeType
       where $Is(this, Tclass.TypeMembers.Color())
         && $IsAlloc(this, Tclass.TypeMembers.Color(), $Heap));
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel_TypeMembers.Color.IsFavorite
     == $LS(MoreFuel_TypeMembers.Color.IsFavorite1);
  free ensures StartFuelAssert_TypeMembers.Color.IsFavorite
     == $LS($LS(MoreFuel_TypeMembers.Color.IsFavorite1));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel_TypeMembers.Color.IsFavorite1)
     == MoreFuel_TypeMembers.Color.IsFavorite1;



procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$TypeMembers.Color.reveal__IsFive();
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel_TypeMembers.Color.IsFive1: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$TypeMembers.Color.reveal__IsFive();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel_TypeMembers.Color.IsFive == $LS(MoreFuel_TypeMembers.Color.IsFive1);
  free ensures StartFuelAssert_TypeMembers.Color.IsFive
     == $LS($LS(MoreFuel_TypeMembers.Color.IsFive1));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel_TypeMembers.Color.IsFive1)
     == MoreFuel_TypeMembers.Color.IsFive1;



function Tclass.TypeMembers.Small() : Ty;

const unique Tagclass.TypeMembers.Small: TyTag;

// Tclass.TypeMembers.Small Tag
axiom Tag(Tclass.TypeMembers.Small()) == Tagclass.TypeMembers.Small
   && TagFamily(Tclass.TypeMembers.Small()) == tytagFamily$Small;

// Box/unbox axiom for Tclass.TypeMembers.Small
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TypeMembers.Small()) } 
  $IsBox(bx, Tclass.TypeMembers.Small())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass.TypeMembers.Small()));

// TypeMembers.Small: newtype $Is
axiom (forall x#0: int :: 
  { $Is(x#0, Tclass.TypeMembers.Small()) } 
  $Is(x#0, Tclass.TypeMembers.Small()) <==> LitInt(30) <= x#0 && x#0 < 40);

// TypeMembers.Small: newtype $IsAlloc
axiom (forall x#0: int, $h: Heap :: 
  { $IsAlloc(x#0, Tclass.TypeMembers.Small(), $h) } 
  $IsAlloc(x#0, Tclass.TypeMembers.Small(), $h));

const unique class.TypeMembers.Small: ClassName;

// function declaration for TypeMembers.Small.IsFavorite
function TypeMembers.Small.IsFavorite($ly: LayerType, this: int) : bool;

function TypeMembers.Small.IsFavorite#canCall(this: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, this: int :: 
  { TypeMembers.Small.IsFavorite($LS($ly), this) } 
  TypeMembers.Small.IsFavorite($LS($ly), this)
     == TypeMembers.Small.IsFavorite($ly, this));

// fuel synonym axiom
axiom (forall $ly: LayerType, this: int :: 
  { TypeMembers.Small.IsFavorite(AsFuelBottom($ly), this) } 
  TypeMembers.Small.IsFavorite($ly, this)
     == TypeMembers.Small.IsFavorite($LZ, this));

// consequence axiom for TypeMembers.Small.IsFavorite
axiom true
   ==> (forall $ly: LayerType, this: int :: 
    { TypeMembers.Small.IsFavorite($ly, this) } 
    TypeMembers.Small.IsFavorite#canCall(this) || (LitInt(30) <= this && this < 40)
       ==> true);

function TypeMembers.Small.IsFavorite#requires(LayerType, int) : bool;

// #requires axiom for TypeMembers.Small.IsFavorite
axiom (forall $ly: LayerType, $Heap: Heap, this: int :: 
  { TypeMembers.Small.IsFavorite#requires($ly, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap) && LitInt(30) <= this && this < 40
     ==> TypeMembers.Small.IsFavorite#requires($ly, this) == true);

// definition axiom for TypeMembers.Small.IsFavorite (revealed)
axiom true
   ==> (forall $ly: LayerType, $Heap: Heap, this: int :: 
    { TypeMembers.Small.IsFavorite($LS($ly), this), $IsGoodHeap($Heap) } 
    TypeMembers.Small.IsFavorite#canCall(this)
         || ($IsGoodHeap($Heap) && LitInt(30) <= this && this < 40)
       ==> TypeMembers.Small.IsFavorite($LS($ly), this) == (this == LitInt(34)));

// definition axiom for TypeMembers.Small.IsFavorite for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, $Heap: Heap, this: int :: 
    {:weight 3} { TypeMembers.Small.IsFavorite($LS($ly), LitInt(this)), $IsGoodHeap($Heap) } 
    TypeMembers.Small.IsFavorite#canCall(LitInt(this))
         || ($IsGoodHeap($Heap) && LitInt(30) <= this && this < 40)
       ==> TypeMembers.Small.IsFavorite($LS($ly), LitInt(this))
         == 
        (LitInt(this)
         == LitInt(34)));

// function declaration for TypeMembers.Small.IsFive
function TypeMembers.Small.IsFive($ly: LayerType, x#0: int) : bool;

function TypeMembers.Small.IsFive#canCall(x#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Small.IsFive($LS($ly), x#0) } 
  TypeMembers.Small.IsFive($LS($ly), x#0) == TypeMembers.Small.IsFive($ly, x#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Small.IsFive(AsFuelBottom($ly), x#0) } 
  TypeMembers.Small.IsFive($ly, x#0) == TypeMembers.Small.IsFive($LZ, x#0));

// consequence axiom for TypeMembers.Small.IsFive
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { TypeMembers.Small.IsFive($ly, x#0) } 
    true ==> true);

function TypeMembers.Small.IsFive#requires(LayerType, int) : bool;

// #requires axiom for TypeMembers.Small.IsFive
axiom (forall $ly: LayerType, x#0: int :: 
  { TypeMembers.Small.IsFive#requires($ly, x#0) } 
  TypeMembers.Small.IsFive#requires($ly, x#0) == true);

// definition axiom for TypeMembers.Small.IsFive (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    { TypeMembers.Small.IsFive($LS($ly), x#0) } 
    true ==> TypeMembers.Small.IsFive($LS($ly), x#0) == (x#0 == LitInt(5)));

// definition axiom for TypeMembers.Small.IsFive for all literals (revealed)
axiom true
   ==> (forall $ly: LayerType, x#0: int :: 
    {:weight 3} { TypeMembers.Small.IsFive($LS($ly), LitInt(x#0)) } 
    true
       ==> TypeMembers.Small.IsFive($LS($ly), LitInt(x#0)) == (LitInt(x#0) == LitInt(5)));

procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$TypeMembers.Small.reveal__IsFavorite(this: int where LitInt(30) <= this && this < 40);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel_TypeMembers.Small.IsFavorite1: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$TypeMembers.Small.reveal__IsFavorite(this: int where LitInt(30) <= this && this < 40);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel_TypeMembers.Small.IsFavorite
     == $LS(MoreFuel_TypeMembers.Small.IsFavorite1);
  free ensures StartFuelAssert_TypeMembers.Small.IsFavorite
     == $LS($LS(MoreFuel_TypeMembers.Small.IsFavorite1));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel_TypeMembers.Small.IsFavorite1)
     == MoreFuel_TypeMembers.Small.IsFavorite1;



procedure {:auto_generated} {:opaque_reveal} {:verify false} CheckWellformed$$TypeMembers.Small.reveal__IsFive();
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



const MoreFuel_TypeMembers.Small.IsFive1: LayerType;

procedure {:auto_generated} {:opaque_reveal} {:verify false} Call$$TypeMembers.Small.reveal__IsFive();
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;
  free ensures StartFuel_TypeMembers.Small.IsFive == $LS(MoreFuel_TypeMembers.Small.IsFive1);
  free ensures StartFuelAssert_TypeMembers.Small.IsFive
     == $LS($LS(MoreFuel_TypeMembers.Small.IsFive1));
  // Shortcut to LZ
  free ensures AsFuelBottom(MoreFuel_TypeMembers.Small.IsFive1)
     == MoreFuel_TypeMembers.Small.IsFive1;



const unique class.TypeMembers.__default: ClassName;

function Tclass.TypeMembers.__default() : Ty;

const unique Tagclass.TypeMembers.__default: TyTag;

// Tclass.TypeMembers.__default Tag
axiom Tag(Tclass.TypeMembers.__default()) == Tagclass.TypeMembers.__default
   && TagFamily(Tclass.TypeMembers.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.TypeMembers.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TypeMembers.__default()) } 
  $IsBox(bx, Tclass.TypeMembers.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TypeMembers.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TypeMembers.__default()) } 
  $Is($o, Tclass.TypeMembers.__default())
     <==> $o == null || dtype($o) == Tclass.TypeMembers.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TypeMembers.__default(), $h) } 
  $IsAlloc($o, Tclass.TypeMembers.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const class.B.X.Abs.__default: ClassName;

function Tclass.B.X.Abs.__default() : Ty;

// Tclass.B.X.Abs.__default Tag
axiom TagFamily(Tclass.B.X.Abs.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.B.X.Abs.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B.X.Abs.__default()) } 
  $IsBox(bx, Tclass.B.X.Abs.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B.X.Abs.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B.X.Abs.__default()) } 
  $Is($o, Tclass.B.X.Abs.__default())
     <==> $o == null || dtype($o) == Tclass.B.X.Abs.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B.X.Abs.__default(), $h) } 
  $IsAlloc($o, Tclass.B.X.Abs.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const class.B.X.Abs.C?: ClassName;

function Tclass.B.X.Abs.C?() : Ty;

// Tclass.B.X.Abs.C? Tag
axiom TagFamily(Tclass.B.X.Abs.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.B.X.Abs.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B.X.Abs.C?()) } 
  $IsBox(bx, Tclass.B.X.Abs.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B.X.Abs.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B.X.Abs.C?()) } 
  $Is($o, Tclass.B.X.Abs.C?()) <==> $o == null || dtype($o) == Tclass.B.X.Abs.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B.X.Abs.C?(), $h) } 
  $IsAlloc($o, Tclass.B.X.Abs.C?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(B.X.Abs.C.x) == 0
   && FieldOfDecl(class.B.X.Abs.C?, field$x) == B.X.Abs.C.x
   && !$IsGhostField(B.X.Abs.C.x);

const B.X.Abs.C.x: Field int;

// C.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, B.X.Abs.C.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.B.X.Abs.C?()
     ==> $Is(read($h, $o, B.X.Abs.C.x), TInt));

// C.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, B.X.Abs.C.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.B.X.Abs.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, B.X.Abs.C.x), TInt, $h));

// function declaration for B.X.Abs.C.Valid
function B.X.Abs.C.Valid($heap: Heap, this: ref) : bool;

function B.X.Abs.C.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.B.X.Abs.C() : Ty;

// Tclass.B.X.Abs.C Tag
axiom TagFamily(Tclass.B.X.Abs.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.B.X.Abs.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B.X.Abs.C()) } 
  $IsBox(bx, Tclass.B.X.Abs.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B.X.Abs.C()));

// frame axiom for B.X.Abs.C.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B.X.Abs.C.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B.X.Abs.C.Valid($h0, this) == B.X.Abs.C.Valid($h1, this));

// consequence axiom for B.X.Abs.C.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B.X.Abs.C.Valid($Heap, this) } 
    B.X.Abs.C.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B.X.Abs.C())
           && $IsAlloc(this, Tclass.B.X.Abs.C(), $Heap))
       ==> (B.X.Abs.C.Valid($Heap, this) ==> LitInt(0) <= read($Heap, this, B.X.Abs.C.x))
         && (read($Heap, this, B.X.Abs.C.x) == LitInt(8) ==> B.X.Abs.C.Valid($Heap, this)));

function B.X.Abs.C.Valid#requires(Heap, ref) : bool;

// #requires axiom for B.X.Abs.C.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { B.X.Abs.C.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B.X.Abs.C())
       && $IsAlloc(this, Tclass.B.X.Abs.C(), $Heap)
     ==> B.X.Abs.C.Valid#requires($Heap, this) == true);

// function declaration for B.X.Abs.C.RevealedValid
function B.X.Abs.C.RevealedValid($heap: Heap, this: ref) : bool;

function B.X.Abs.C.RevealedValid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for B.X.Abs.C.RevealedValid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B.X.Abs.C.RevealedValid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B.X.Abs.C.RevealedValid($h0, this) == B.X.Abs.C.RevealedValid($h1, this));

// consequence axiom for B.X.Abs.C.RevealedValid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B.X.Abs.C.RevealedValid($Heap, this) } 
    B.X.Abs.C.RevealedValid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B.X.Abs.C())
           && $IsAlloc(this, Tclass.B.X.Abs.C(), $Heap))
       ==> (B.X.Abs.C.Valid($Heap, this) ==> LitInt(0) <= read($Heap, this, B.X.Abs.C.x))
         && (read($Heap, this, B.X.Abs.C.x) == LitInt(8) ==> B.X.Abs.C.Valid($Heap, this)));

function B.X.Abs.C.RevealedValid#requires(Heap, ref) : bool;

// #requires axiom for B.X.Abs.C.RevealedValid
axiom (forall $Heap: Heap, this: ref :: 
  { B.X.Abs.C.RevealedValid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B.X.Abs.C())
       && $IsAlloc(this, Tclass.B.X.Abs.C(), $Heap)
     ==> B.X.Abs.C.RevealedValid#requires($Heap, this) == true);

// function declaration for B.X.Abs.C.Get
function B.X.Abs.C.Get($heap: Heap, this: ref) : int;

function B.X.Abs.C.Get#canCall($heap: Heap, this: ref) : bool;

// frame axiom for B.X.Abs.C.Get
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B.X.Abs.C.Get($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B.X.Abs.C.Get($h0, this) == B.X.Abs.C.Get($h1, this));

// consequence axiom for B.X.Abs.C.Get
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B.X.Abs.C.Get($Heap, this) } 
    B.X.Abs.C.Get#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B.X.Abs.C())
           && $IsAlloc(this, Tclass.B.X.Abs.C(), $Heap))
       ==> true);

function B.X.Abs.C.Get#requires(Heap, ref) : bool;

// #requires axiom for B.X.Abs.C.Get
axiom (forall $Heap: Heap, this: ref :: 
  { B.X.Abs.C.Get#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B.X.Abs.C())
       && $IsAlloc(this, Tclass.B.X.Abs.C(), $Heap)
     ==> B.X.Abs.C.Get#requires($Heap, this) == true);

// B.X.Abs.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.B.X.Abs.C()) } 
  $Is(c#0, Tclass.B.X.Abs.C()) <==> $Is(c#0, Tclass.B.X.Abs.C?()) && c#0 != null);

// B.X.Abs.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.B.X.Abs.C(), $h) } 
  $IsAlloc(c#0, Tclass.B.X.Abs.C(), $h)
     <==> $IsAlloc(c#0, Tclass.B.X.Abs.C?(), $h));

const class.B____direct.X.Abs.__default: ClassName;

function Tclass.B____direct.X.Abs.__default() : Ty;

// Tclass.B____direct.X.Abs.__default Tag
axiom TagFamily(Tclass.B____direct.X.Abs.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.B____direct.X.Abs.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B____direct.X.Abs.__default()) } 
  $IsBox(bx, Tclass.B____direct.X.Abs.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.B____direct.X.Abs.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B____direct.X.Abs.__default()) } 
  $Is($o, Tclass.B____direct.X.Abs.__default())
     <==> $o == null || dtype($o) == Tclass.B____direct.X.Abs.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B____direct.X.Abs.__default(), $h) } 
  $IsAlloc($o, Tclass.B____direct.X.Abs.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const class.B____direct.X.Abs.C?: ClassName;

function Tclass.B____direct.X.Abs.C?() : Ty;

// Tclass.B____direct.X.Abs.C? Tag
axiom TagFamily(Tclass.B____direct.X.Abs.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.B____direct.X.Abs.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B____direct.X.Abs.C?()) } 
  $IsBox(bx, Tclass.B____direct.X.Abs.C?())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.B____direct.X.Abs.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B____direct.X.Abs.C?()) } 
  $Is($o, Tclass.B____direct.X.Abs.C?())
     <==> $o == null || dtype($o) == Tclass.B____direct.X.Abs.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B____direct.X.Abs.C?(), $h) } 
  $IsAlloc($o, Tclass.B____direct.X.Abs.C?(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for B__direct.X.Abs.C.Valid
function B____direct.X.Abs.C.Valid($heap: Heap, this: ref) : bool;

function B____direct.X.Abs.C.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.B____direct.X.Abs.C() : Ty;

// Tclass.B____direct.X.Abs.C Tag
axiom TagFamily(Tclass.B____direct.X.Abs.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.B____direct.X.Abs.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B____direct.X.Abs.C()) } 
  $IsBox(bx, Tclass.B____direct.X.Abs.C())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.B____direct.X.Abs.C()));

// frame axiom for B____direct.X.Abs.C.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B____direct.X.Abs.C.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B____direct.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B____direct.X.Abs.C.Valid($h0, this) == B____direct.X.Abs.C.Valid($h1, this));

axiom FDim(B____direct.X.Abs.C.x) == 0
   && FieldOfDecl(class.B____direct.X.Abs.C?, field$x) == B____direct.X.Abs.C.x
   && !$IsGhostField(B____direct.X.Abs.C.x);

// consequence axiom for B____direct.X.Abs.C.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____direct.X.Abs.C.Valid($Heap, this) } 
    B____direct.X.Abs.C.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____direct.X.Abs.C())
           && $IsAlloc(this, Tclass.B____direct.X.Abs.C(), $Heap))
       ==> (B____direct.X.Abs.C.Valid($Heap, this)
           ==> LitInt(0) <= read($Heap, this, B____direct.X.Abs.C.x))
         && (read($Heap, this, B____direct.X.Abs.C.x) == LitInt(8)
           ==> B____direct.X.Abs.C.Valid($Heap, this)));

function B____direct.X.Abs.C.Valid#requires(Heap, ref) : bool;

// #requires axiom for B____direct.X.Abs.C.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { B____direct.X.Abs.C.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B____direct.X.Abs.C())
       && $IsAlloc(this, Tclass.B____direct.X.Abs.C(), $Heap)
     ==> B____direct.X.Abs.C.Valid#requires($Heap, this) == true);

// function declaration for B__direct.X.Abs.C.RevealedValid
function B____direct.X.Abs.C.RevealedValid($heap: Heap, this: ref) : bool;

function B____direct.X.Abs.C.RevealedValid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for B____direct.X.Abs.C.RevealedValid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B____direct.X.Abs.C.RevealedValid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B____direct.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B____direct.X.Abs.C.RevealedValid($h0, this)
       == B____direct.X.Abs.C.RevealedValid($h1, this));

// consequence axiom for B____direct.X.Abs.C.RevealedValid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____direct.X.Abs.C.RevealedValid($Heap, this) } 
    B____direct.X.Abs.C.RevealedValid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____direct.X.Abs.C())
           && $IsAlloc(this, Tclass.B____direct.X.Abs.C(), $Heap))
       ==> (B____direct.X.Abs.C.Valid($Heap, this)
           ==> LitInt(0) <= read($Heap, this, B____direct.X.Abs.C.x))
         && (read($Heap, this, B____direct.X.Abs.C.x) == LitInt(8)
           ==> B____direct.X.Abs.C.Valid($Heap, this)));

function B____direct.X.Abs.C.RevealedValid#requires(Heap, ref) : bool;

// #requires axiom for B____direct.X.Abs.C.RevealedValid
axiom (forall $Heap: Heap, this: ref :: 
  { B____direct.X.Abs.C.RevealedValid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B____direct.X.Abs.C())
       && $IsAlloc(this, Tclass.B____direct.X.Abs.C(), $Heap)
     ==> B____direct.X.Abs.C.RevealedValid#requires($Heap, this) == true);

// definition axiom for B____direct.X.Abs.C.RevealedValid (revealed)
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____direct.X.Abs.C.RevealedValid($Heap, this), $IsGoodHeap($Heap) } 
    B____direct.X.Abs.C.RevealedValid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____direct.X.Abs.C())
           && $IsAlloc(this, Tclass.B____direct.X.Abs.C(), $Heap))
       ==> B____direct.X.Abs.C.RevealedValid($Heap, this)
         == 
        (read($Heap, this, B____direct.X.Abs.C.x)
         == LitInt(8)));

const B____direct.X.Abs.C.x: Field int;

// C.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, B____direct.X.Abs.C.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.B____direct.X.Abs.C?()
     ==> $Is(read($h, $o, B____direct.X.Abs.C.x), TInt));

// C.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, B____direct.X.Abs.C.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.B____direct.X.Abs.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, B____direct.X.Abs.C.x), TInt, $h));

// function declaration for B__direct.X.Abs.C.Get
function B____direct.X.Abs.C.Get($heap: Heap, this: ref) : int;

function B____direct.X.Abs.C.Get#canCall($heap: Heap, this: ref) : bool;

// frame axiom for B____direct.X.Abs.C.Get
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B____direct.X.Abs.C.Get($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B____direct.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B____direct.X.Abs.C.Get($h0, this) == B____direct.X.Abs.C.Get($h1, this));

// consequence axiom for B____direct.X.Abs.C.Get
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____direct.X.Abs.C.Get($Heap, this) } 
    B____direct.X.Abs.C.Get#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____direct.X.Abs.C())
           && $IsAlloc(this, Tclass.B____direct.X.Abs.C(), $Heap))
       ==> true);

function B____direct.X.Abs.C.Get#requires(Heap, ref) : bool;

// #requires axiom for B____direct.X.Abs.C.Get
axiom (forall $Heap: Heap, this: ref :: 
  { B____direct.X.Abs.C.Get#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B____direct.X.Abs.C())
       && $IsAlloc(this, Tclass.B____direct.X.Abs.C(), $Heap)
     ==> B____direct.X.Abs.C.Get#requires($Heap, this) == true);

// B__direct.X.Abs.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.B____direct.X.Abs.C()) } 
  $Is(c#0, Tclass.B____direct.X.Abs.C())
     <==> $Is(c#0, Tclass.B____direct.X.Abs.C?()) && c#0 != null);

// B__direct.X.Abs.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.B____direct.X.Abs.C(), $h) } 
  $IsAlloc(c#0, Tclass.B____direct.X.Abs.C(), $h)
     <==> $IsAlloc(c#0, Tclass.B____direct.X.Abs.C?(), $h));

const class.B____more.X.Abs.__default: ClassName;

function Tclass.B____more.X.Abs.__default() : Ty;

// Tclass.B____more.X.Abs.__default Tag
axiom TagFamily(Tclass.B____more.X.Abs.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.B____more.X.Abs.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B____more.X.Abs.__default()) } 
  $IsBox(bx, Tclass.B____more.X.Abs.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.B____more.X.Abs.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B____more.X.Abs.__default()) } 
  $Is($o, Tclass.B____more.X.Abs.__default())
     <==> $o == null || dtype($o) == Tclass.B____more.X.Abs.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B____more.X.Abs.__default(), $h) } 
  $IsAlloc($o, Tclass.B____more.X.Abs.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

const class.B____more.X.Abs.C?: ClassName;

function Tclass.B____more.X.Abs.C?() : Ty;

// Tclass.B____more.X.Abs.C? Tag
axiom TagFamily(Tclass.B____more.X.Abs.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass.B____more.X.Abs.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B____more.X.Abs.C?()) } 
  $IsBox(bx, Tclass.B____more.X.Abs.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B____more.X.Abs.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.B____more.X.Abs.C?()) } 
  $Is($o, Tclass.B____more.X.Abs.C?())
     <==> $o == null || dtype($o) == Tclass.B____more.X.Abs.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.B____more.X.Abs.C?(), $h) } 
  $IsAlloc($o, Tclass.B____more.X.Abs.C?(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for B__more.X.Abs.C.Valid
function B____more.X.Abs.C.Valid($heap: Heap, this: ref) : bool;

function B____more.X.Abs.C.Valid#canCall($heap: Heap, this: ref) : bool;

function Tclass.B____more.X.Abs.C() : Ty;

// Tclass.B____more.X.Abs.C Tag
axiom TagFamily(Tclass.B____more.X.Abs.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass.B____more.X.Abs.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.B____more.X.Abs.C()) } 
  $IsBox(bx, Tclass.B____more.X.Abs.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass.B____more.X.Abs.C()));

// frame axiom for B____more.X.Abs.C.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B____more.X.Abs.C.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B____more.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B____more.X.Abs.C.Valid($h0, this) == B____more.X.Abs.C.Valid($h1, this));

axiom FDim(B____more.X.Abs.C.x) == 0
   && FieldOfDecl(class.B____more.X.Abs.C?, field$x) == B____more.X.Abs.C.x
   && !$IsGhostField(B____more.X.Abs.C.x);

// consequence axiom for B____more.X.Abs.C.Valid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____more.X.Abs.C.Valid($Heap, this) } 
    B____more.X.Abs.C.Valid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____more.X.Abs.C())
           && $IsAlloc(this, Tclass.B____more.X.Abs.C(), $Heap))
       ==> (B____more.X.Abs.C.Valid($Heap, this)
           ==> LitInt(0) <= read($Heap, this, B____more.X.Abs.C.x))
         && (read($Heap, this, B____more.X.Abs.C.x) == LitInt(8)
           ==> B____more.X.Abs.C.Valid($Heap, this)));

function B____more.X.Abs.C.Valid#requires(Heap, ref) : bool;

// #requires axiom for B____more.X.Abs.C.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { B____more.X.Abs.C.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B____more.X.Abs.C())
       && $IsAlloc(this, Tclass.B____more.X.Abs.C(), $Heap)
     ==> B____more.X.Abs.C.Valid#requires($Heap, this) == true);

// function declaration for B__more.X.Abs.C.RevealedValid
function B____more.X.Abs.C.RevealedValid($heap: Heap, this: ref) : bool;

function B____more.X.Abs.C.RevealedValid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for B____more.X.Abs.C.RevealedValid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B____more.X.Abs.C.RevealedValid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B____more.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B____more.X.Abs.C.RevealedValid($h0, this)
       == B____more.X.Abs.C.RevealedValid($h1, this));

// consequence axiom for B____more.X.Abs.C.RevealedValid
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____more.X.Abs.C.RevealedValid($Heap, this) } 
    B____more.X.Abs.C.RevealedValid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____more.X.Abs.C())
           && $IsAlloc(this, Tclass.B____more.X.Abs.C(), $Heap))
       ==> (B____more.X.Abs.C.Valid($Heap, this)
           ==> LitInt(0) <= read($Heap, this, B____more.X.Abs.C.x))
         && (read($Heap, this, B____more.X.Abs.C.x) == LitInt(8)
           ==> B____more.X.Abs.C.Valid($Heap, this)));

function B____more.X.Abs.C.RevealedValid#requires(Heap, ref) : bool;

// #requires axiom for B____more.X.Abs.C.RevealedValid
axiom (forall $Heap: Heap, this: ref :: 
  { B____more.X.Abs.C.RevealedValid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B____more.X.Abs.C())
       && $IsAlloc(this, Tclass.B____more.X.Abs.C(), $Heap)
     ==> B____more.X.Abs.C.RevealedValid#requires($Heap, this) == true);

// definition axiom for B____more.X.Abs.C.RevealedValid (revealed)
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____more.X.Abs.C.RevealedValid($Heap, this), $IsGoodHeap($Heap) } 
    B____more.X.Abs.C.RevealedValid#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____more.X.Abs.C())
           && $IsAlloc(this, Tclass.B____more.X.Abs.C(), $Heap))
       ==> B____more.X.Abs.C.RevealedValid($Heap, this)
         == 
        (read($Heap, this, B____more.X.Abs.C.x)
         == LitInt(8)));

const B____more.X.Abs.C.x: Field int;

// C.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, B____more.X.Abs.C.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass.B____more.X.Abs.C?()
     ==> $Is(read($h, $o, B____more.X.Abs.C.x), TInt));

// C.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, B____more.X.Abs.C.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass.B____more.X.Abs.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, B____more.X.Abs.C.x), TInt, $h));

// function declaration for B__more.X.Abs.C.Get
function B____more.X.Abs.C.Get($heap: Heap, this: ref) : int;

function B____more.X.Abs.C.Get#canCall($heap: Heap, this: ref) : bool;

// frame axiom for B____more.X.Abs.C.Get
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), B____more.X.Abs.C.Get($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass.B____more.X.Abs.C())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null && $o == this ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> B____more.X.Abs.C.Get($h0, this) == B____more.X.Abs.C.Get($h1, this));

// consequence axiom for B____more.X.Abs.C.Get
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____more.X.Abs.C.Get($Heap, this) } 
    B____more.X.Abs.C.Get#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____more.X.Abs.C())
           && $IsAlloc(this, Tclass.B____more.X.Abs.C(), $Heap))
       ==> true);

function B____more.X.Abs.C.Get#requires(Heap, ref) : bool;

// #requires axiom for B____more.X.Abs.C.Get
axiom (forall $Heap: Heap, this: ref :: 
  { B____more.X.Abs.C.Get#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass.B____more.X.Abs.C())
       && $IsAlloc(this, Tclass.B____more.X.Abs.C(), $Heap)
     ==> B____more.X.Abs.C.Get#requires($Heap, this) == true);

// definition axiom for B____more.X.Abs.C.Get (revealed)
axiom true
   ==> (forall $Heap: Heap, this: ref :: 
    { B____more.X.Abs.C.Get($Heap, this), $IsGoodHeap($Heap) } 
    B____more.X.Abs.C.Get#canCall($Heap, this)
         || ($IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass.B____more.X.Abs.C())
           && $IsAlloc(this, Tclass.B____more.X.Abs.C(), $Heap))
       ==> B____more.X.Abs.C.Get($Heap, this) == read($Heap, this, B____more.X.Abs.C.x));

// B__more.X.Abs.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass.B____more.X.Abs.C()) } 
  $Is(c#0, Tclass.B____more.X.Abs.C())
     <==> $Is(c#0, Tclass.B____more.X.Abs.C?()) && c#0 != null);

// B__more.X.Abs.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass.B____more.X.Abs.C(), $h) } 
  $IsAlloc(c#0, Tclass.B____more.X.Abs.C(), $h)
     <==> $IsAlloc(c#0, Tclass.B____more.X.Abs.C?(), $h));

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

const unique tytagFamily$Box: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Tr: TyTagFamily;

const unique tytagFamily$Color: TyTagFamily;

const unique tytagFamily$Small: TyTagFamily;

const unique field$x: NameFamily;
