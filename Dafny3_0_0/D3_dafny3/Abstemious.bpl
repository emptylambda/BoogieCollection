// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy -print:./Abstemious.bpl

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
function #_module.List.ListCons(Box, DatatypeType) : DatatypeType;

const unique ##_module.List.ListCons: DtCtorId;

// Constructor identifier
axiom (forall a#19#0#0: Box, a#19#1#0: DatatypeType :: 
  { #_module.List.ListCons(a#19#0#0, a#19#1#0) } 
  DatatypeCtorId(#_module.List.ListCons(a#19#0#0, a#19#1#0))
     == ##_module.List.ListCons);

function _module.List.ListCons_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { _module.List.ListCons_q(d) } 
  _module.List.ListCons_q(d) <==> DatatypeCtorId(d) == ##_module.List.ListCons);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { _module.List.ListCons_q(d) } 
  _module.List.ListCons_q(d)
     ==> (exists a#20#0#0: Box, a#20#1#0: DatatypeType :: 
      d == #_module.List.ListCons(a#20#0#0, a#20#1#0)));

// Constructor $Is
axiom (forall _module.List$T: Ty, a#21#0#0: Box, a#21#1#0: DatatypeType :: 
  { $Is(#_module.List.ListCons(a#21#0#0, a#21#1#0), Tclass._module.List(_module.List$T)) } 
  $Is(#_module.List.ListCons(a#21#0#0, a#21#1#0), Tclass._module.List(_module.List$T))
     <==> $IsBox(a#21#0#0, _module.List$T)
       && $Is(a#21#1#0, Tclass._module.List(_module.List$T)));

// Constructor $IsAlloc
axiom (forall _module.List$T: Ty, a#22#0#0: Box, a#22#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.List.ListCons(a#22#0#0, a#22#1#0), 
      Tclass._module.List(_module.List$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.List.ListCons(a#22#0#0, a#22#1#0), 
        Tclass._module.List(_module.List$T), 
        $h)
       <==> $IsAllocBox(a#22#0#0, _module.List$T, $h)
         && $IsAlloc(a#22#1#0, Tclass._module.List(_module.List$T), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAllocBox(_module.List.head(d), _module.List$T, $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.ListCons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAllocBox(_module.List.head(d), _module.List$T, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, _module.List$T: Ty, $h: Heap :: 
  { $IsAlloc(_module.List.tail(d), Tclass._module.List(_module.List$T), $h) } 
  $IsGoodHeap($h)
       && 
      _module.List.ListCons_q(d)
       && $IsAlloc(d, Tclass._module.List(_module.List$T), $h)
     ==> $IsAlloc(_module.List.tail(d), Tclass._module.List(_module.List$T), $h));

// Constructor literal
axiom (forall a#23#0#0: Box, a#23#1#0: DatatypeType :: 
  { #_module.List.ListCons(Lit(a#23#0#0), Lit(a#23#1#0)) } 
  #_module.List.ListCons(Lit(a#23#0#0), Lit(a#23#1#0))
     == Lit(#_module.List.ListCons(a#23#0#0, a#23#1#0)));

function _module.List.head(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#24#0#0: Box, a#24#1#0: DatatypeType :: 
  { #_module.List.ListCons(a#24#0#0, a#24#1#0) } 
  _module.List.head(#_module.List.ListCons(a#24#0#0, a#24#1#0)) == a#24#0#0);

// Inductive rank
axiom (forall a#25#0#0: Box, a#25#1#0: DatatypeType :: 
  { #_module.List.ListCons(a#25#0#0, a#25#1#0) } 
  BoxRank(a#25#0#0) < DtRank(#_module.List.ListCons(a#25#0#0, a#25#1#0)));

function _module.List.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#26#0#0: Box, a#26#1#0: DatatypeType :: 
  { #_module.List.ListCons(a#26#0#0, a#26#1#0) } 
  _module.List.tail(#_module.List.ListCons(a#26#0#0, a#26#1#0)) == a#26#1#0);

// Inductive rank
axiom (forall a#27#0#0: Box, a#27#1#0: DatatypeType :: 
  { #_module.List.ListCons(a#27#0#0, a#27#1#0) } 
  DtRank(a#27#1#0) < DtRank(#_module.List.ListCons(a#27#0#0, a#27#1#0)));

// Depth-one case-split function
function $IsA#_module.List(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#_module.List(d) } 
  $IsA#_module.List(d) ==> _module.List.Nil_q(d) || _module.List.ListCons_q(d));

// Questionmark data type disjunctivity
axiom (forall _module.List$T: Ty, d: DatatypeType :: 
  { _module.List.ListCons_q(d), $Is(d, Tclass._module.List(_module.List$T)) } 
    { _module.List.Nil_q(d), $Is(d, Tclass._module.List(_module.List$T)) } 
  $Is(d, Tclass._module.List(_module.List$T))
     ==> _module.List.Nil_q(d) || _module.List.ListCons_q(d));

// Datatype extensional equality declaration
function _module.List#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #_module.List.Nil
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b), _module.List.Nil_q(a) } 
    { _module.List#Equal(a, b), _module.List.Nil_q(b) } 
  _module.List.Nil_q(a) && _module.List.Nil_q(b)
     ==> (_module.List#Equal(a, b) <==> true));

// Datatype extensional equality definition: #_module.List.ListCons
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b), _module.List.ListCons_q(a) } 
    { _module.List#Equal(a, b), _module.List.ListCons_q(b) } 
  _module.List.ListCons_q(a) && _module.List.ListCons_q(b)
     ==> (_module.List#Equal(a, b)
       <==> _module.List.head(a) == _module.List.head(b)
         && _module.List#Equal(_module.List.tail(a), _module.List.tail(b))));

// Datatype extensionality axiom: _module.List
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { _module.List#Equal(a, b) } 
  _module.List#Equal(a, b) <==> a == b);

const unique class._module.List: ClassName;

// Constructor function declaration
function #_module.Stream.Cons(Box, DatatypeType) : DatatypeType;

const unique ##_module.Stream.Cons: DtCtorId;

// Constructor identifier
axiom (forall a#28#0#0: Box, a#28#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#28#0#0, a#28#1#0) } 
  DatatypeCtorId(#_module.Stream.Cons(a#28#0#0, a#28#1#0))
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
     ==> (exists a#29#0#0: Box, a#29#1#0: DatatypeType :: 
      d == #_module.Stream.Cons(a#29#0#0, a#29#1#0)));

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
axiom (forall _module.Stream$T: Ty, a#30#0#0: Box, a#30#1#0: DatatypeType :: 
  { $Is(#_module.Stream.Cons(a#30#0#0, a#30#1#0), 
      Tclass._module.Stream(_module.Stream$T)) } 
  $Is(#_module.Stream.Cons(a#30#0#0, a#30#1#0), 
      Tclass._module.Stream(_module.Stream$T))
     <==> $IsBox(a#30#0#0, _module.Stream$T)
       && $Is(a#30#1#0, Tclass._module.Stream(_module.Stream$T)));

// Constructor $IsAlloc
axiom (forall _module.Stream$T: Ty, a#31#0#0: Box, a#31#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#_module.Stream.Cons(a#31#0#0, a#31#1#0), 
      Tclass._module.Stream(_module.Stream$T), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#_module.Stream.Cons(a#31#0#0, a#31#1#0), 
        Tclass._module.Stream(_module.Stream$T), 
        $h)
       <==> $IsAllocBox(a#31#0#0, _module.Stream$T, $h)
         && $IsAlloc(a#31#1#0, Tclass._module.Stream(_module.Stream$T), $h)));

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
axiom (forall a#32#0#0: Box, a#32#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#32#0#0, a#32#1#0) } 
  _module.Stream.head(#_module.Stream.Cons(a#32#0#0, a#32#1#0)) == a#32#0#0);

function _module.Stream.tail(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#33#0#0: Box, a#33#1#0: DatatypeType :: 
  { #_module.Stream.Cons(a#33#0#0, a#33#1#0) } 
  _module.Stream.tail(#_module.Stream.Cons(a#33#0#0, a#33#1#0)) == a#33#1#0);

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
  free requires 39 == $FunctionContextHeight;
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
  free requires 39 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



function _module.__default.plus1#Handle() : HandleType;

axiom (forall $heap: Heap, $fh$0x#0: Box :: 
  { Apply1(TInt, TInt, $heap, _module.__default.plus1#Handle(), $fh$0x#0) } 
  Apply1(TInt, TInt, $heap, _module.__default.plus1#Handle(), $fh$0x#0)
     == $Box(_module.__default.plus1($Unbox($fh$0x#0): int)));

axiom (forall $heap: Heap, $fh$0x#0: Box :: 
  { Requires1(TInt, TInt, $heap, _module.__default.plus1#Handle(), $fh$0x#0) } 
  Requires1(TInt, TInt, $heap, _module.__default.plus1#Handle(), $fh$0x#0)
     == _module.__default.plus1#requires($Unbox($fh$0x#0): int));

axiom (forall $bx: Box, $heap: Heap, $fh$0x#0: Box :: 
  { Reads1(TInt, TInt, $heap, _module.__default.plus1#Handle(), $fh$0x#0)[$bx] } 
  Reads1(TInt, TInt, $heap, _module.__default.plus1#Handle(), $fh$0x#0)[$bx]
     == false);

axiom (forall $heap: Heap, $fh$0x#0: int :: 
  { _module.__default.plus1($fh$0x#0), $IsGoodHeap($heap) } 
  _module.__default.plus1($fh$0x#0)
     == $Unbox(Apply1(TInt, TInt, $heap, _module.__default.plus1#Handle(), $Box($fh$0x#0))): int);

function _module.__default.plus#Handle() : HandleType;

axiom (forall $heap: Heap, $fh$0x#0: Box, $fh$0x#1: Box :: 
  { Apply2(TInt, TInt, TInt, $heap, _module.__default.plus#Handle(), $fh$0x#0, $fh$0x#1) } 
  Apply2(TInt, TInt, TInt, $heap, _module.__default.plus#Handle(), $fh$0x#0, $fh$0x#1)
     == $Box(_module.__default.plus($Unbox($fh$0x#0): int, $Unbox($fh$0x#1): int)));

axiom (forall $heap: Heap, $fh$0x#0: Box, $fh$0x#1: Box :: 
  { Requires2(TInt, TInt, TInt, $heap, _module.__default.plus#Handle(), $fh$0x#0, $fh$0x#1) } 
  Requires2(TInt, TInt, TInt, $heap, _module.__default.plus#Handle(), $fh$0x#0, $fh$0x#1)
     == _module.__default.plus#requires($Unbox($fh$0x#0): int, $Unbox($fh$0x#1): int));

axiom (forall $bx: Box, $heap: Heap, $fh$0x#0: Box, $fh$0x#1: Box :: 
  { Reads2(TInt, TInt, TInt, $heap, _module.__default.plus#Handle(), $fh$0x#0, $fh$0x#1)[$bx] } 
  Reads2(TInt, TInt, TInt, $heap, _module.__default.plus#Handle(), $fh$0x#0, $fh$0x#1)[$bx]
     == false);

axiom (forall $heap: Heap, $fh$0x#0: int, $fh$0x#1: int :: 
  { _module.__default.plus($fh$0x#0, $fh$0x#1), $IsGoodHeap($heap) } 
  _module.__default.plus($fh$0x#0, $fh$0x#1)
     == $Unbox(Apply2(TInt, 
        TInt, 
        TInt, 
        $heap, 
        _module.__default.plus#Handle(), 
        $Box($fh$0x#0), 
        $Box($fh$0x#1))): int);

implementation Impl$$_module.__default._default_Main() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var n#0: int;
  var n##0: int;
  var msg##0: Seq Box;
  var s##0: DatatypeType;
  var n##1: int;
  var msg##1: Seq Box;
  var s##1: DatatypeType;
  var ##n#0: int;
  var n##2: int;
  var msg##2: Seq Box;
  var s##2: DatatypeType;
  var ##f#0: HandleType;
  var ##s#0: DatatypeType;
  var n##3: int;
  var msg##3: Seq Box;
  var s##3: DatatypeType;
  var ##n#1: int;
  var ##f#1: HandleType;
  var ##s#1: DatatypeType;
  var n##4: int;
  var msg##4: Seq Box;
  var s##4: DatatypeType;
  var msg##5: Seq Box;
  var s##5: DatatypeType;
  var ##n#2: int;
  var ##n#3: int;
  var ##s#2: DatatypeType;
  var n##5: int;
  var msg##6: Seq Box;
  var s##6: DatatypeType;
  var ##n#4: int;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var n##6: int;
  var msg##7: Seq Box;
  var s##7: DatatypeType;
  var ##n#5: int;
  var ##a#1: DatatypeType;
  var ##b#1: DatatypeType;
  var ##a#2: DatatypeType;
  var n##7: int;
  var msg##8: Seq Box;
  var s##8: DatatypeType;
  var n##8: int;
  var msg##9: Seq Box;
  var s##9: DatatypeType;
  var ##n#6: int;
  var ##a#3: DatatypeType;
  var ##b#2: DatatypeType;
  var n##9: int;
  var msg##10: Seq Box;
  var s##10: DatatypeType;
  var n##10: int;
  var msg##11: Seq Box;
  var s##11: DatatypeType;
  var n##11: int;
  var msg##12: Seq Box;
  var s##12: DatatypeType;
  var n##12: int;
  var msg##13: Seq Box;
  var s##13: DatatypeType;
  var n##13: int;
  var msg##14: Seq Box;
  var s##14: DatatypeType;
  var ##n#7: int;
  var ##f#2: HandleType;
  var ##a#4: DatatypeType;
  var ##b#3: DatatypeType;

    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(7,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(8,9)
    assume true;
    assume true;
    n#0 := LitInt(7);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(8,12)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(9,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##0 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##0 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(111))), 
                $Box(char#FromInt(110))), 
              $Box(char#FromInt(101))), 
            $Box(char#FromInt(115))), 
          $Box(char#FromInt(40))), 
        $Box(char#FromInt(41))));
    assume _module.__default.ones#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LZ))));
    assume _module.__default.ones#canCall();
    // ProcessCallStmt: CheckSubrange
    s##0 := Lit(_module.__default.ones($LS($LZ)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##0, msg##0, s##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(9,28)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(10,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##1 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##1 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(102))), 
                  $Box(char#FromInt(114))), 
                $Box(char#FromInt(111))), 
              $Box(char#FromInt(109))), 
            $Box(char#FromInt(40))), 
          $Box(char#FromInt(51))), 
        $Box(char#FromInt(41))));
    ##n#0 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, TInt, $Heap);
    assume _module.__default.from#canCall(LitInt(3));
    assume _module.Stream.Cons_q(Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assume _module.__default.from#canCall(LitInt(3));
    // ProcessCallStmt: CheckSubrange
    s##1 := Lit(_module.__default.from($LS($LZ), LitInt(3)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##1, msg##1, s##1);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(10,30)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(11,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##2 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##2 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(77))), $Box(char#FromInt(97))), 
                                      $Box(char#FromInt(112))), 
                                    $Box(char#FromInt(40))), 
                                  $Box(char#FromInt(112))), 
                                $Box(char#FromInt(108))), 
                              $Box(char#FromInt(117))), 
                            $Box(char#FromInt(115))), 
                          $Box(char#FromInt(49))), 
                        $Box(char#FromInt(44))), 
                      $Box(char#FromInt(32))), 
                    $Box(char#FromInt(111))), 
                  $Box(char#FromInt(110))), 
                $Box(char#FromInt(101))), 
              $Box(char#FromInt(115))), 
            $Box(char#FromInt(40))), 
          $Box(char#FromInt(41))), 
        $Box(char#FromInt(41))));
    assert 38 != $FunctionContextHeight;
    assume _module.__default.ones#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LZ))));
    ##f#0 := _module.__default.plus1#Handle();
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap);
    ##s#0 := Lit(_module.__default.ones($LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.Map#canCall(TInt, 
      TInt, 
      _module.__default.plus1#Handle(), 
      Lit(_module.__default.ones($LS($LZ))));
    assume _module.Stream.Cons_q(_module.__default.Map(TInt, 
        TInt, 
        $LS($LZ), 
        _module.__default.plus1#Handle(), 
        Lit(_module.__default.ones($LS($LZ)))));
    assume _module.__default.ones#canCall()
       && _module.__default.Map#canCall(TInt, 
        TInt, 
        _module.__default.plus1#Handle(), 
        Lit(_module.__default.ones($LS($LZ))));
    // ProcessCallStmt: CheckSubrange
    s##2 := _module.__default.Map(TInt, 
      TInt, 
      $LS($LZ), 
      _module.__default.plus1#Handle(), 
      Lit(_module.__default.ones($LS($LZ))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##2, msg##2, s##2);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(11,52)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(12,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##3 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##3 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(77))), $Box(char#FromInt(97))), 
                                        $Box(char#FromInt(112))), 
                                      $Box(char#FromInt(40))), 
                                    $Box(char#FromInt(112))), 
                                  $Box(char#FromInt(108))), 
                                $Box(char#FromInt(117))), 
                              $Box(char#FromInt(115))), 
                            $Box(char#FromInt(49))), 
                          $Box(char#FromInt(44))), 
                        $Box(char#FromInt(32))), 
                      $Box(char#FromInt(102))), 
                    $Box(char#FromInt(114))), 
                  $Box(char#FromInt(111))), 
                $Box(char#FromInt(109))), 
              $Box(char#FromInt(40))), 
            $Box(char#FromInt(51))), 
          $Box(char#FromInt(41))), 
        $Box(char#FromInt(41))));
    assert 38 != $FunctionContextHeight;
    ##n#1 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, TInt, $Heap);
    assume _module.__default.from#canCall(LitInt(3));
    assume _module.Stream.Cons_q(Lit(_module.__default.from($LS($LZ), LitInt(3))));
    ##f#1 := _module.__default.plus1#Handle();
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#1, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap);
    ##s#1 := Lit(_module.__default.from($LS($LZ), LitInt(3)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#1, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.Map#canCall(TInt, 
      TInt, 
      _module.__default.plus1#Handle(), 
      Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assume _module.Stream.Cons_q(_module.__default.Map(TInt, 
        TInt, 
        $LS($LZ), 
        _module.__default.plus1#Handle(), 
        Lit(_module.__default.from($LS($LZ), LitInt(3)))));
    assume _module.__default.from#canCall(LitInt(3))
       && _module.__default.Map#canCall(TInt, 
        TInt, 
        _module.__default.plus1#Handle(), 
        Lit(_module.__default.from($LS($LZ), LitInt(3))));
    // ProcessCallStmt: CheckSubrange
    s##3 := _module.__default.Map(TInt, 
      TInt, 
      $LS($LZ), 
      _module.__default.plus1#Handle(), 
      Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##3, msg##3, s##3);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(12,54)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(13,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##4 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##4 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(115))), 
                      $Box(char#FromInt(113))), 
                    $Box(char#FromInt(117))), 
                  $Box(char#FromInt(97))), 
                $Box(char#FromInt(114))), 
              $Box(char#FromInt(101))), 
            $Box(char#FromInt(115))), 
          $Box(char#FromInt(40))), 
        $Box(char#FromInt(41))));
    assume _module.__default.squares#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.squares()));
    assume _module.__default.squares#canCall();
    // ProcessCallStmt: CheckSubrange
    s##4 := Lit(_module.__default.squares());
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##4, msg##4, s##4);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(13,34)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(14,12)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##5 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(116))), $Box(char#FromInt(97))), 
                                  $Box(char#FromInt(107))), 
                                $Box(char#FromInt(101))), 
                              $Box(char#FromInt(40))), 
                            $Box(char#FromInt(53))), 
                          $Box(char#FromInt(44))), 
                        $Box(char#FromInt(32))), 
                      $Box(char#FromInt(102))), 
                    $Box(char#FromInt(114))), 
                  $Box(char#FromInt(111))), 
                $Box(char#FromInt(109))), 
              $Box(char#FromInt(40))), 
            $Box(char#FromInt(51))), 
          $Box(char#FromInt(41))), 
        $Box(char#FromInt(41))));
    ##n#2 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, TInt, $Heap);
    assume _module.__default.from#canCall(LitInt(3));
    assume _module.Stream.Cons_q(Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assert $Is(LitInt(5), Tclass._System.nat());
    ##n#3 := LitInt(5);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#3, Tclass._System.nat(), $Heap);
    ##s#2 := Lit(_module.__default.from($LS($LZ), LitInt(3)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#2, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.take#canCall(TInt, LitInt(5), Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assume _module.__default.from#canCall(LitInt(3))
       && _module.__default.take#canCall(TInt, LitInt(5), Lit(_module.__default.from($LS($LZ), LitInt(3))));
    // ProcessCallStmt: CheckSubrange
    s##5 := Lit(_module.__default.take(TInt, $LS($LZ), LitInt(5), Lit(_module.__default.from($LS($LZ), LitInt(3)))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.PrintList(TInt, msg##5, s##5);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(14,49)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(15,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##5 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##6 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(122))), 
                                          $Box(char#FromInt(105))), 
                                        $Box(char#FromInt(112))), 
                                      $Box(char#FromInt(40))), 
                                    $Box(char#FromInt(111))), 
                                  $Box(char#FromInt(110))), 
                                $Box(char#FromInt(101))), 
                              $Box(char#FromInt(115))), 
                            $Box(char#FromInt(40))), 
                          $Box(char#FromInt(41))), 
                        $Box(char#FromInt(44))), 
                      $Box(char#FromInt(32))), 
                    $Box(char#FromInt(102))), 
                  $Box(char#FromInt(114))), 
                $Box(char#FromInt(111))), 
              $Box(char#FromInt(109))), 
            $Box(char#FromInt(40))), 
          $Box(char#FromInt(51))), 
        $Box(char#FromInt(41))));
    assume _module.__default.ones#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LZ))));
    ##n#4 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#4, TInt, $Heap);
    assume _module.__default.from#canCall(LitInt(3));
    assume _module.Stream.Cons_q(Lit(_module.__default.from($LS($LZ), LitInt(3))));
    ##a#0 := Lit(_module.__default.ones($LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, Tclass._module.Stream(TInt), $Heap);
    ##b#0 := Lit(_module.__default.from($LS($LZ), LitInt(3)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.zip#canCall(TInt, 
      TInt, 
      Lit(_module.__default.ones($LS($LZ))), 
      Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assume _module.Stream.Cons_q(Lit(_module.__default.zip(TInt, 
          TInt, 
          $LS($LZ), 
          Lit(_module.__default.ones($LS($LZ))), 
          Lit(_module.__default.from($LS($LZ), LitInt(3))))));
    assume _module.__default.ones#canCall()
       && _module.__default.from#canCall(LitInt(3))
       && _module.__default.zip#canCall(TInt, 
        TInt, 
        Lit(_module.__default.ones($LS($LZ))), 
        Lit(_module.__default.from($LS($LZ), LitInt(3))));
    // ProcessCallStmt: CheckSubrange
    s##6 := Lit(_module.__default.zip(TInt, 
        TInt, 
        $LS($LZ), 
        Lit(_module.__default.ones($LS($LZ))), 
        Lit(_module.__default.from($LS($LZ), LitInt(3)))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(Tclass._System.Tuple2(TInt, TInt), n##5, msg##6, s##6);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(15,55)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(16,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##6 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##7 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(97))), $Box(char#FromInt(100))), 
                                                          $Box(char#FromInt(100))), 
                                                        $Box(char#FromInt(80))), 
                                                      $Box(char#FromInt(97))), 
                                                    $Box(char#FromInt(105))), 
                                                  $Box(char#FromInt(114))), 
                                                $Box(char#FromInt(40))), 
                                              $Box(char#FromInt(122))), 
                                            $Box(char#FromInt(105))), 
                                          $Box(char#FromInt(112))), 
                                        $Box(char#FromInt(40))), 
                                      $Box(char#FromInt(111))), 
                                    $Box(char#FromInt(110))), 
                                  $Box(char#FromInt(101))), 
                                $Box(char#FromInt(115))), 
                              $Box(char#FromInt(40))), 
                            $Box(char#FromInt(41))), 
                          $Box(char#FromInt(44))), 
                        $Box(char#FromInt(32))), 
                      $Box(char#FromInt(102))), 
                    $Box(char#FromInt(114))), 
                  $Box(char#FromInt(111))), 
                $Box(char#FromInt(109))), 
              $Box(char#FromInt(40))), 
            $Box(char#FromInt(51))), 
          $Box(char#FromInt(41))), 
        $Box(char#FromInt(41))));
    assume _module.__default.ones#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LZ))));
    ##n#5 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#5, TInt, $Heap);
    assume _module.__default.from#canCall(LitInt(3));
    assume _module.Stream.Cons_q(Lit(_module.__default.from($LS($LZ), LitInt(3))));
    ##a#1 := Lit(_module.__default.ones($LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, Tclass._module.Stream(TInt), $Heap);
    ##b#1 := Lit(_module.__default.from($LS($LZ), LitInt(3)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.zip#canCall(TInt, 
      TInt, 
      Lit(_module.__default.ones($LS($LZ))), 
      Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assume _module.Stream.Cons_q(Lit(_module.__default.zip(TInt, 
          TInt, 
          $LS($LZ), 
          Lit(_module.__default.ones($LS($LZ))), 
          Lit(_module.__default.from($LS($LZ), LitInt(3))))));
    ##a#2 := Lit(_module.__default.zip(TInt, 
        TInt, 
        $LS($LZ), 
        Lit(_module.__default.ones($LS($LZ))), 
        Lit(_module.__default.from($LS($LZ), LitInt(3)))));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#2, Tclass._module.Stream(Tclass._System.Tuple2(TInt, TInt)), $Heap);
    assume _module.__default.addPair#canCall(Lit(_module.__default.zip(TInt, 
          TInt, 
          $LS($LZ), 
          Lit(_module.__default.ones($LS($LZ))), 
          Lit(_module.__default.from($LS($LZ), LitInt(3))))));
    assume _module.Stream.Cons_q(Lit(_module.__default.addPair($LS($LZ), 
          Lit(_module.__default.zip(TInt, 
              TInt, 
              $LS($LZ), 
              Lit(_module.__default.ones($LS($LZ))), 
              Lit(_module.__default.from($LS($LZ), LitInt(3))))))));
    assume _module.__default.ones#canCall()
       && _module.__default.from#canCall(LitInt(3))
       && _module.__default.zip#canCall(TInt, 
        TInt, 
        Lit(_module.__default.ones($LS($LZ))), 
        Lit(_module.__default.from($LS($LZ), LitInt(3))))
       && _module.__default.addPair#canCall(Lit(_module.__default.zip(TInt, 
            TInt, 
            $LS($LZ), 
            Lit(_module.__default.ones($LS($LZ))), 
            Lit(_module.__default.from($LS($LZ), LitInt(3))))));
    // ProcessCallStmt: CheckSubrange
    s##7 := Lit(_module.__default.addPair($LS($LZ), 
        Lit(_module.__default.zip(TInt, 
            TInt, 
            $LS($LZ), 
            Lit(_module.__default.ones($LS($LZ))), 
            Lit(_module.__default.from($LS($LZ), LitInt(3)))))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##6, msg##7, s##7);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(16,73)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(17,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##7 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##8 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(102))), 
              $Box(char#FromInt(105))), 
            $Box(char#FromInt(98))), 
          $Box(char#FromInt(40))), 
        $Box(char#FromInt(41))));
    assume _module.__default.fib#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.fib($LS($LZ))));
    assume _module.__default.fib#canCall();
    // ProcessCallStmt: CheckSubrange
    s##8 := Lit(_module.__default.fib($LS($LZ)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##7, msg##8, s##8);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(17,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(18,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##8 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##9 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(97))), $Box(char#FromInt(100))), 
                                          $Box(char#FromInt(100))), 
                                        $Box(char#FromInt(40))), 
                                      $Box(char#FromInt(111))), 
                                    $Box(char#FromInt(110))), 
                                  $Box(char#FromInt(101))), 
                                $Box(char#FromInt(115))), 
                              $Box(char#FromInt(40))), 
                            $Box(char#FromInt(41))), 
                          $Box(char#FromInt(44))), 
                        $Box(char#FromInt(32))), 
                      $Box(char#FromInt(102))), 
                    $Box(char#FromInt(114))), 
                  $Box(char#FromInt(111))), 
                $Box(char#FromInt(109))), 
              $Box(char#FromInt(40))), 
            $Box(char#FromInt(51))), 
          $Box(char#FromInt(41))), 
        $Box(char#FromInt(41))));
    assume _module.__default.ones#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LZ))));
    ##n#6 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#6, TInt, $Heap);
    assume _module.__default.from#canCall(LitInt(3));
    assume _module.Stream.Cons_q(Lit(_module.__default.from($LS($LZ), LitInt(3))));
    ##a#3 := Lit(_module.__default.ones($LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#3, Tclass._module.Stream(TInt), $Heap);
    ##b#2 := Lit(_module.__default.from($LS($LZ), LitInt(3)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#2, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.add#canCall(Lit(_module.__default.ones($LS($LZ))), 
      Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assume _module.Stream.Cons_q(Lit(_module.__default.add($LS($LZ), 
          Lit(_module.__default.ones($LS($LZ))), 
          Lit(_module.__default.from($LS($LZ), LitInt(3))))));
    assume _module.__default.ones#canCall()
       && _module.__default.from#canCall(LitInt(3))
       && _module.__default.add#canCall(Lit(_module.__default.ones($LS($LZ))), 
        Lit(_module.__default.from($LS($LZ), LitInt(3))));
    // ProcessCallStmt: CheckSubrange
    s##9 := Lit(_module.__default.add($LS($LZ), 
        Lit(_module.__default.ones($LS($LZ))), 
        Lit(_module.__default.from($LS($LZ), LitInt(3)))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##8, msg##9, s##9);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(18,56)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(19,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##9 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##10 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(70))), $Box(char#FromInt(105))), 
            $Box(char#FromInt(98))), 
          $Box(char#FromInt(40))), 
        $Box(char#FromInt(41))));
    assume _module.__default.Fib#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
    assume _module.__default.Fib#canCall();
    // ProcessCallStmt: CheckSubrange
    s##10 := Lit(_module.__default.Fib($LS($LZ)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##9, msg##10, s##10);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(19,26)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(20,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##10 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##11 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(70))), $Box(char#FromInt(105))), 
              $Box(char#FromInt(98))), 
            $Box(char#FromInt(48))), 
          $Box(char#FromInt(40))), 
        $Box(char#FromInt(41))));
    assume _module.__default.Fib0#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.Fib0($LS($LZ))));
    assume _module.__default.Fib0#canCall();
    // ProcessCallStmt: CheckSubrange
    s##11 := Lit(_module.__default.Fib0($LS($LZ)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##10, msg##11, s##11);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(20,28)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(21,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##11 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##12 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(70))), $Box(char#FromInt(105))), 
              $Box(char#FromInt(98))), 
            $Box(char#FromInt(49))), 
          $Box(char#FromInt(40))), 
        $Box(char#FromInt(41))));
    assume _module.__default.Fib1#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.Fib1($LS($LZ))));
    assume _module.__default.Fib1#canCall();
    // ProcessCallStmt: CheckSubrange
    s##12 := Lit(_module.__default.Fib1($LS($LZ)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##11, msg##12, s##12);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(21,28)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(22,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##12 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##13 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(79))), $Box(char#FromInt(104))), 
                  $Box(char#FromInt(79))), 
                $Box(char#FromInt(110))), 
              $Box(char#FromInt(101))), 
            $Box(char#FromInt(115))), 
          $Box(char#FromInt(40))), 
        $Box(char#FromInt(41))));
    assume _module.__default.OhOnes#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LZ))));
    assume _module.__default.OhOnes#canCall();
    // ProcessCallStmt: CheckSubrange
    s##13 := Lit(_module.__default.OhOnes($LS($LZ)));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##12, msg##13, s##13);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(22,32)"} true;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(23,8)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    assert $Is(n#0, Tclass._System.nat());
    n##13 := n#0;
    assume true;
    // ProcessCallStmt: CheckSubrange
    msg##14 := Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(char#FromInt(67))), $Box(char#FromInt(111))), 
                                                              $Box(char#FromInt(109))), 
                                                            $Box(char#FromInt(98))), 
                                                          $Box(char#FromInt(105))), 
                                                        $Box(char#FromInt(110))), 
                                                      $Box(char#FromInt(101))), 
                                                    $Box(char#FromInt(40))), 
                                                  $Box(char#FromInt(112))), 
                                                $Box(char#FromInt(108))), 
                                              $Box(char#FromInt(117))), 
                                            $Box(char#FromInt(115))), 
                                          $Box(char#FromInt(44))), 
                                        $Box(char#FromInt(32))), 
                                      $Box(char#FromInt(111))), 
                                    $Box(char#FromInt(110))), 
                                  $Box(char#FromInt(101))), 
                                $Box(char#FromInt(115))), 
                              $Box(char#FromInt(40))), 
                            $Box(char#FromInt(41))), 
                          $Box(char#FromInt(44))), 
                        $Box(char#FromInt(32))), 
                      $Box(char#FromInt(102))), 
                    $Box(char#FromInt(114))), 
                  $Box(char#FromInt(111))), 
                $Box(char#FromInt(109))), 
              $Box(char#FromInt(40))), 
            $Box(char#FromInt(51))), 
          $Box(char#FromInt(41))), 
        $Box(char#FromInt(41))));
    assert 9 != $FunctionContextHeight;
    assume _module.__default.ones#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LZ))));
    ##n#7 := LitInt(3);
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#7, TInt, $Heap);
    assume _module.__default.from#canCall(LitInt(3));
    assume _module.Stream.Cons_q(Lit(_module.__default.from($LS($LZ), LitInt(3))));
    ##f#2 := _module.__default.plus#Handle();
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#2, Tclass._System.___hTotalFunc2(TInt, TInt, TInt), $Heap);
    ##a#4 := Lit(_module.__default.ones($LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#4, Tclass._module.Stream(TInt), $Heap);
    ##b#3 := Lit(_module.__default.from($LS($LZ), LitInt(3)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#3, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.Combine#canCall(TInt, 
      _module.__default.plus#Handle(), 
      Lit(_module.__default.ones($LS($LZ))), 
      Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assume _module.Stream.Cons_q(_module.__default.Combine(TInt, 
        $LS($LZ), 
        _module.__default.plus#Handle(), 
        Lit(_module.__default.ones($LS($LZ))), 
        Lit(_module.__default.from($LS($LZ), LitInt(3)))));
    assume _module.__default.ones#canCall()
       && _module.__default.from#canCall(LitInt(3))
       && _module.__default.Combine#canCall(TInt, 
        _module.__default.plus#Handle(), 
        Lit(_module.__default.ones($LS($LZ))), 
        Lit(_module.__default.from($LS($LZ), LitInt(3))));
    // ProcessCallStmt: CheckSubrange
    s##14 := _module.__default.Combine(TInt, 
      $LS($LZ), 
      _module.__default.plus#Handle(), 
      Lit(_module.__default.ones($LS($LZ))), 
      Lit(_module.__default.from($LS($LZ), LitInt(3))));
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.Print(TInt, n##13, msg##14, s##14);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(23,76)"} true;
}



procedure CheckWellformed$$_module.__default.Print(_module._default.Print$T: Ty, 
    n#0: int where LitInt(0) <= n#0, 
    msg#0: Seq Box
       where $Is(msg#0, TSeq(TChar)) && $IsAlloc(msg#0, TSeq(TChar), $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Print$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Print$T), $Heap)
         && $IsA#_module.Stream(s#0));
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Print(_module._default.Print$T: Ty, 
    n#0: int where LitInt(0) <= n#0, 
    msg#0: Seq Box
       where $Is(msg#0, TSeq(TChar)) && $IsAlloc(msg#0, TSeq(TChar), $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Print$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Print$T), $Heap)
         && $IsA#_module.Stream(s#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Print(_module._default.Print$T: Ty, 
    n#0: int where LitInt(0) <= n#0, 
    msg#0: Seq Box
       where $Is(msg#0, TSeq(TChar)) && $IsAlloc(msg#0, TSeq(TChar), $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.Print$T))
         && $IsAlloc(s#0, Tclass._module.Stream(_module._default.Print$T), $Heap)
         && $IsA#_module.Stream(s#0))
   returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Print(_module._default.Print$T: Ty, n#0: int, msg#0: Seq Box, s#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var i#0: int;
  var s#1: DatatypeType
     where $Is(s#1, Tclass._module.Stream(_module._default.Print$T))
       && $IsAlloc(s#1, Tclass._module.Stream(_module._default.Print$T), $Heap);
  var $rhs#0: int;
  var $rhs#1: DatatypeType
     where $Is($rhs#1, Tclass._module.Stream(_module._default.Print$T));
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;
  var $rhs#0_0: int;
  var $rhs#0_1: DatatypeType
     where $Is($rhs#0_1, Tclass._module.Stream(_module._default.Print$T));

    // AddMethodImpl: Print, Impl$$_module.__default.Print
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(26,51): initial state"} true;
    $_reverifyPost := false;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(27,3)
    assume true;
    assume true;
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(28,12)
    assume true;
    assume true;
    assume true;
    $rhs#0 := LitInt(0);
    assume true;
    $rhs#1 := s#0;
    i#0 := $rhs#0;
    s#1 := $rhs#1;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(28,18)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(29,3)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := n#0 - i#0;
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
      free invariant n#0 - i#0 <= $decr_init$loop#00 && (n#0 - i#0 == $decr_init$loop#00 ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(29,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume true;
        if (n#0 <= i#0)
        {
            break;
        }

        $decr$loop#00 := n#0 - i#0;
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(30,5)
        assume _module.Stream.Cons_q(s#1);
        assume _module.Stream.Cons_q(s#1);
        assume true;
        // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(31,10)
        assume true;
        assume true;
        assume true;
        $rhs#0_0 := i#0 + 1;
        assume _module.Stream.Cons_q(s#1);
        assume _module.Stream.Cons_q(s#1);
        $rhs#0_1 := _module.Stream.tail(s#1);
        i#0 := $rhs#0_0;
        s#1 := $rhs#0_1;
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(31,25)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(29,3)
        assert 0 <= $decr$loop#00 || n#0 - i#0 == $decr$loop#00;
        assert n#0 - i#0 < $decr$loop#00;
    }

    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(33,3)
    assume true;
}



procedure CheckWellformed$$_module.__default.PrintList(_module._default.PrintList$T: Ty, 
    msg#0: Seq Box
       where $Is(msg#0, TSeq(TChar)) && $IsAlloc(msg#0, TSeq(TChar), $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.List(_module._default.PrintList$T))
         && $IsAlloc(s#0, Tclass._module.List(_module._default.PrintList$T), $Heap)
         && $IsA#_module.List(s#0));
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.PrintList(_module._default.PrintList$T: Ty, 
    msg#0: Seq Box
       where $Is(msg#0, TSeq(TChar)) && $IsAlloc(msg#0, TSeq(TChar), $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.List(_module._default.PrintList$T))
         && $IsAlloc(s#0, Tclass._module.List(_module._default.PrintList$T), $Heap)
         && $IsA#_module.List(s#0));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.PrintList(_module._default.PrintList$T: Ty, 
    msg#0: Seq Box
       where $Is(msg#0, TSeq(TChar)) && $IsAlloc(msg#0, TSeq(TChar), $Heap), 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.List(_module._default.PrintList$T))
         && $IsAlloc(s#0, Tclass._module.List(_module._default.PrintList$T), $Heap)
         && $IsA#_module.List(s#0))
   returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.PrintList(_module._default.PrintList$T: Ty, msg#0: Seq Box, s#0: DatatypeType)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var s#1: DatatypeType
     where $Is(s#1, Tclass._module.List(_module._default.PrintList$T))
       && $IsAlloc(s#1, Tclass._module.List(_module._default.PrintList$T), $Heap);
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: DatatypeType;
  var $w$loop#0: bool;
  var $decr$loop#00: DatatypeType;

    // AddMethodImpl: PrintList, Impl$$_module.__default.PrintList
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(36,45): initial state"} true;
    $_reverifyPost := false;
    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(37,3)
    assume true;
    assume true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(38,9)
    assume true;
    assume true;
    s#1 := s#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(38,12)"} true;
    // ----- while statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(39,3)
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
      free invariant DtRank(s#1) <= DtRank($decr_init$loop#00)
         && (DtRank(s#1) == DtRank($decr_init$loop#00) ==> true);
    {
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(39,2): after some loop iterations"} true;
        if (!$w$loop#0)
        {
            assume true;
            assume false;
        }

        assume $IsA#_module.List(s#1);
        if (_module.List#Equal(s#1, #_module.List.Nil()))
        {
            break;
        }

        $decr$loop#00 := s#1;
        // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(42,5)
        assert _module.List.ListCons_q(s#1);
        assume true;
        assume true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(43,7)
        assume true;
        assert _module.List.ListCons_q(s#1);
        assume true;
        s#1 := _module.List.tail(s#1);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(43,15)"} true;
        // ----- loop termination check ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(39,3)
        assert DtRank(s#1) < DtRank($decr$loop#00);
    }

    // ----- print statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(45,3)
    assume true;
}



// function declaration for _module._default.plus1
function _module.__default.plus1(x#0: int) : int;

function _module.__default.plus1#canCall(x#0: int) : bool;

// consequence axiom for _module.__default.plus1
axiom 38 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.plus1(x#0) } 
    _module.__default.plus1#canCall(x#0) || 38 != $FunctionContextHeight ==> true);

function _module.__default.plus1#requires(int) : bool;

// #requires axiom for _module.__default.plus1
axiom (forall x#0: int :: 
  { _module.__default.plus1#requires(x#0) } 
  _module.__default.plus1#requires(x#0) == true);

// definition axiom for _module.__default.plus1 (revealed)
axiom 38 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    { _module.__default.plus1(x#0) } 
    _module.__default.plus1#canCall(x#0) || 38 != $FunctionContextHeight
       ==> _module.__default.plus1(x#0) == x#0 + 1);

// definition axiom for _module.__default.plus1 for all literals (revealed)
axiom 38 <= $FunctionContextHeight
   ==> (forall x#0: int :: 
    {:weight 3} { _module.__default.plus1(LitInt(x#0)) } 
    _module.__default.plus1#canCall(LitInt(x#0)) || 38 != $FunctionContextHeight
       ==> _module.__default.plus1(LitInt(x#0)) == LitInt(x#0 + 1));

procedure CheckWellformed$$_module.__default.plus1(x#0: int);
  free requires 38 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for _module._default.plus
function _module.__default.plus(x#0: int, y#0: int) : int;

function _module.__default.plus#canCall(x#0: int, y#0: int) : bool;

// consequence axiom for _module.__default.plus
axiom 9 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: int :: 
    { _module.__default.plus(x#0, y#0) } 
    _module.__default.plus#canCall(x#0, y#0) || 9 != $FunctionContextHeight ==> true);

function _module.__default.plus#requires(int, int) : bool;

// #requires axiom for _module.__default.plus
axiom (forall x#0: int, y#0: int :: 
  { _module.__default.plus#requires(x#0, y#0) } 
  _module.__default.plus#requires(x#0, y#0) == true);

// definition axiom for _module.__default.plus (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: int :: 
    { _module.__default.plus(x#0, y#0) } 
    _module.__default.plus#canCall(x#0, y#0) || 9 != $FunctionContextHeight
       ==> _module.__default.plus(x#0, y#0) == x#0 + y#0);

// definition axiom for _module.__default.plus for all literals (revealed)
axiom 9 <= $FunctionContextHeight
   ==> (forall x#0: int, y#0: int :: 
    {:weight 3} { _module.__default.plus(LitInt(x#0), LitInt(y#0)) } 
    _module.__default.plus#canCall(LitInt(x#0), LitInt(y#0))
         || 9 != $FunctionContextHeight
       ==> _module.__default.plus(LitInt(x#0), LitInt(y#0)) == LitInt(x#0 + y#0));

procedure CheckWellformed$$_module.__default.plus(x#0: int, y#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



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
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.ones($ly) } 
    _module.__default.ones#canCall() || 2 != $FunctionContextHeight
       ==> $Is(_module.__default.ones($ly), Tclass._module.Stream(TInt)));

function _module.__default.ones#requires(LayerType) : bool;

// #requires axiom for _module.__default.ones
axiom (forall $ly: LayerType :: 
  { _module.__default.ones#requires($ly) } 
  _module.__default.ones#requires($ly) == true);

// definition axiom for _module.__default.ones (revealed)
axiom 2 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.ones($LS($ly)) } 
    _module.__default.ones#canCall() || 2 != $FunctionContextHeight
       ==> _module.__default.ones#canCall()
         && _module.__default.ones($LS($ly))
           == Lit(#_module.Stream.Cons($Box(LitInt(1)), Lit(_module.__default.ones($ly)))));

procedure CheckWellformed$$_module.__default.ones();
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.ones()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function ones
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(54,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.ones($LS($LZ)), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.ones#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LZ))));
        assume _module.__default.ones($LS($LZ))
           == Lit(#_module.Stream.Cons($Box(LitInt(1)), Lit(_module.__default.ones($LS($LZ)))));
        assume _module.__default.ones#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.ones($LS($LZ)), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.from
function _module.__default.from($ly: LayerType, n#0: int) : DatatypeType;

function _module.__default.from#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.from($LS($ly), n#0) } 
  _module.__default.from($LS($ly), n#0) == _module.__default.from($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.from(AsFuelBottom($ly), n#0) } 
  _module.__default.from($ly, n#0) == _module.__default.from($LZ, n#0));

// consequence axiom for _module.__default.from
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.from($ly, n#0) } 
    _module.__default.from#canCall(n#0) || 18 != $FunctionContextHeight
       ==> $Is(_module.__default.from($ly, n#0), Tclass._module.Stream(TInt)));

function _module.__default.from#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.from
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.from#requires($ly, n#0) } 
  _module.__default.from#requires($ly, n#0) == true);

// definition axiom for _module.__default.from (revealed)
axiom 18 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.from($LS($ly), n#0) } 
    _module.__default.from#canCall(n#0) || 18 != $FunctionContextHeight
       ==> _module.__default.from#canCall(n#0 + 1)
         && _module.__default.from($LS($ly), n#0)
           == #_module.Stream.Cons($Box(n#0), _module.__default.from($ly, n#0 + 1)));

procedure CheckWellformed$$_module.__default.from(n#0: int);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.from(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function from
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(59,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.from($LS($LZ), n#0), Tclass._module.Stream(TInt));
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
        assume _module.__default.from#canCall(n#0 + 1);
        assume _module.Stream.Cons_q(_module.__default.from($LS($LZ), n#0 + 1));
        assume _module.__default.from($LS($LZ), n#0)
           == #_module.Stream.Cons($Box(n#0), _module.__default.from($LS($LZ), n#0 + 1));
        assume _module.__default.from#canCall(n#0 + 1);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.from($LS($LZ), n#0), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Map
function _module.__default.Map(_module._default.Map$T: Ty, 
    _module._default.Map$U: Ty, 
    $ly: LayerType, 
    f#0: HandleType, 
    s#0: DatatypeType)
   : DatatypeType;

function _module.__default.Map#canCall(_module._default.Map$T: Ty, 
    _module._default.Map$U: Ty, 
    f#0: HandleType, 
    s#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.Map$T: Ty, 
    _module._default.Map$U: Ty, 
    $ly: LayerType, 
    f#0: HandleType, 
    s#0: DatatypeType :: 
  { _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $LS($ly), f#0, s#0) } 
  _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $LS($ly), f#0, s#0)
     == _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $ly, f#0, s#0));

// fuel synonym axiom
axiom (forall _module._default.Map$T: Ty, 
    _module._default.Map$U: Ty, 
    $ly: LayerType, 
    f#0: HandleType, 
    s#0: DatatypeType :: 
  { _module.__default.Map(_module._default.Map$T, _module._default.Map$U, AsFuelBottom($ly), f#0, s#0) } 
  _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $ly, f#0, s#0)
     == _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $LZ, f#0, s#0));

// consequence axiom for _module.__default.Map
axiom 20 <= $FunctionContextHeight
   ==> (forall _module._default.Map$T: Ty, 
      _module._default.Map$U: Ty, 
      $ly: LayerType, 
      f#0: HandleType, 
      s#0: DatatypeType :: 
    { _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $ly, f#0, s#0) } 
    _module.__default.Map#canCall(_module._default.Map$T, _module._default.Map$U, f#0, s#0)
         || (20 != $FunctionContextHeight
           && 
          $Is(f#0, 
            Tclass._System.___hTotalFunc1(_module._default.Map$T, _module._default.Map$U))
           && $Is(s#0, Tclass._module.Stream(_module._default.Map$T)))
       ==> $Is(_module.__default.Map(_module._default.Map$T, _module._default.Map$U, $ly, f#0, s#0), 
        Tclass._module.Stream(_module._default.Map$U)));

function _module.__default.Map#requires(Ty, Ty, LayerType, HandleType, DatatypeType) : bool;

// #requires axiom for _module.__default.Map
axiom (forall _module._default.Map$T: Ty, 
    _module._default.Map$U: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    f#0: HandleType, 
    s#0: DatatypeType :: 
  { _module.__default.Map#requires(_module._default.Map$T, _module._default.Map$U, $ly, f#0, s#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(f#0, 
        Tclass._System.___hTotalFunc1(_module._default.Map$T, _module._default.Map$U))
       && $Is(s#0, Tclass._module.Stream(_module._default.Map$T))
     ==> _module.__default.Map#requires(_module._default.Map$T, _module._default.Map$U, $ly, f#0, s#0)
       == true);

// definition axiom for _module.__default.Map (revealed)
axiom 20 <= $FunctionContextHeight
   ==> (forall _module._default.Map$T: Ty, 
      _module._default.Map$U: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      f#0: HandleType, 
      s#0: DatatypeType :: 
    { _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $LS($ly), f#0, s#0), $IsGoodHeap($Heap) } 
    _module.__default.Map#canCall(_module._default.Map$T, _module._default.Map$U, f#0, s#0)
         || (20 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, 
            Tclass._System.___hTotalFunc1(_module._default.Map$T, _module._default.Map$U))
           && $Is(s#0, Tclass._module.Stream(_module._default.Map$T)))
       ==> _module.Stream.Cons_q(s#0)
         && 
        _module.Stream.Cons_q(s#0)
         && _module.__default.Map#canCall(_module._default.Map$T, _module._default.Map$U, f#0, _module.Stream.tail(s#0))
         && _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $LS($ly), f#0, s#0)
           == #_module.Stream.Cons(Apply1(_module._default.Map$T, 
              _module._default.Map$U, 
              $Heap, 
              f#0, 
              _module.Stream.head(s#0)), 
            _module.__default.Map(_module._default.Map$T, 
              _module._default.Map$U, 
              $ly, 
              f#0, 
              _module.Stream.tail(s#0))));

procedure CheckWellformed$$_module.__default.Map(_module._default.Map$T: Ty, 
    _module._default.Map$U: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hTotalFunc1(_module._default.Map$T, _module._default.Map$U)), 
    s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(_module._default.Map$T)));
  free requires 20 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Map(_module._default.Map$T: Ty, 
    _module._default.Map$U: Ty, 
    f#0: HandleType, 
    s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##f#0: HandleType;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Map
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(64,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Map(_module._default.Map$T, _module._default.Map$U, $LS($LZ), f#0, s#0), 
          Tclass._module.Stream(_module._default.Map$U));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(s#0);
        assume _module.Stream.Cons_q(s#0);
        ##f#0 := f#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#0, 
          Tclass._System.___hTotalFunc1(_module._default.Map$T, _module._default.Map$U), 
          $Heap);
        ##s#0 := _module.Stream.tail(s#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.Map$T), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Map#canCall(_module._default.Map$T, _module._default.Map$U, f#0, _module.Stream.tail(s#0));
        assume _module.Stream.Cons_q(_module.__default.Map(_module._default.Map$T, 
            _module._default.Map$U, 
            $LS($LZ), 
            f#0, 
            _module.Stream.tail(s#0)));
        assume _module.__default.Map(_module._default.Map$T, _module._default.Map$U, $LS($LZ), f#0, s#0)
           == #_module.Stream.Cons(Apply1(_module._default.Map$T, 
              _module._default.Map$U, 
              $Heap, 
              f#0, 
              _module.Stream.head(s#0)), 
            _module.__default.Map(_module._default.Map$T, 
              _module._default.Map$U, 
              $LS($LZ), 
              f#0, 
              _module.Stream.tail(s#0)));
        assume _module.Stream.Cons_q(s#0)
           && 
          _module.Stream.Cons_q(s#0)
           && _module.__default.Map#canCall(_module._default.Map$T, _module._default.Map$U, f#0, _module.Stream.tail(s#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Map(_module._default.Map$T, _module._default.Map$U, $LS($LZ), f#0, s#0), 
          Tclass._module.Stream(_module._default.Map$U));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.squares
function _module.__default.squares() : DatatypeType;

function _module.__default.squares#canCall() : bool;

// consequence axiom for _module.__default.squares
axiom 21 <= $FunctionContextHeight
   ==> 
  _module.__default.squares#canCall() || 21 != $FunctionContextHeight
   ==> $Is(_module.__default.squares(), Tclass._module.Stream(TInt));

function _module.__default.squares#requires() : bool;

// #requires axiom for _module.__default.squares
axiom _module.__default.squares#requires() == true;

// definition axiom for _module.__default.squares (revealed)
axiom 21 <= $FunctionContextHeight
   ==> 
  _module.__default.squares#canCall() || 21 != $FunctionContextHeight
   ==> _module.__default.from#canCall(LitInt(0))
     && _module.__default.Map#canCall(TInt, 
      TInt, 
      Lit(AtLayer((lambda $l#2#ly#0: LayerType :: 
            Handle1((lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                $Box(Mul($Unbox($l#2#x#0): int, $Unbox($l#2#x#0): int))), 
              (lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: $IsBox($l#2#x#0, TInt)), 
              (lambda $l#2#heap#0: Heap, $l#2#x#0: Box :: 
                SetRef_to_SetBox((lambda $l#2#o#0: ref :: false))))), 
          $LS($LZ))), 
      Lit(_module.__default.from($LS($LZ), LitInt(0))))
     && _module.__default.squares()
       == Lit(_module.__default.Map(TInt, 
          TInt, 
          $LS($LZ), 
          Lit(AtLayer((lambda $l#0#ly#0: LayerType :: 
                Handle1((lambda $l#0#heap#0: Heap, $l#0#x#0: Box :: 
                    $Box(Mul($Unbox($l#0#x#0): int, $Unbox($l#0#x#0): int))), 
                  (lambda $l#0#heap#0: Heap, $l#0#x#0: Box :: $IsBox($l#0#x#0, TInt)), 
                  (lambda $l#0#heap#0: Heap, $l#0#x#0: Box :: 
                    SetRef_to_SetBox((lambda $l#0#o#0: ref :: false))))), 
              $LS($LZ))), 
          Lit(_module.__default.from($LS($LZ), LitInt(0)))));

// definition axiom for _module.__default.squares for all literals (revealed)
axiom 21 <= $FunctionContextHeight
   ==> 
  _module.__default.squares#canCall() || 21 != $FunctionContextHeight
   ==> _module.__default.from#canCall(LitInt(0))
     && _module.__default.Map#canCall(TInt, 
      TInt, 
      Lit(AtLayer((lambda $l#5#ly#0: LayerType :: 
            Handle1((lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                $Box(Mul($Unbox($l#5#x#0): int, $Unbox($l#5#x#0): int))), 
              (lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: $IsBox($l#5#x#0, TInt)), 
              (lambda $l#5#heap#0: Heap, $l#5#x#0: Box :: 
                SetRef_to_SetBox((lambda $l#5#o#0: ref :: false))))), 
          $LS($LZ))), 
      Lit(_module.__default.from($LS($LZ), LitInt(0))))
     && _module.__default.squares()
       == Lit(_module.__default.Map(TInt, 
          TInt, 
          $LS($LZ), 
          Lit(AtLayer((lambda $l#3#ly#0: LayerType :: 
                Handle1((lambda $l#3#heap#0: Heap, $l#3#x#0: Box :: 
                    $Box(Mul($Unbox($l#3#x#0): int, $Unbox($l#3#x#0): int))), 
                  (lambda $l#3#heap#0: Heap, $l#3#x#0: Box :: $IsBox($l#3#x#0, TInt)), 
                  (lambda $l#3#heap#0: Heap, $l#3#x#0: Box :: 
                    SetRef_to_SetBox((lambda $l#3#o#0: ref :: false))))), 
              $LS($LZ))), 
          Lit(_module.__default.from($LS($LZ), LitInt(0)))));

procedure CheckWellformed$$_module.__default.squares();
  free requires 21 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.squares()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0: int;
  var $oldHeap#0: Heap;
  var $_Frame#l0: <beta>[ref,Field beta]bool;
  var lambdaResult#0: int;
  var ##n#0: int;
  var ##f#0: HandleType;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function squares
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(69,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.squares(), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        // Begin Comprehension WF check
        if (*)
        {
            havoc x#0;
            if (true)
            {
                $oldHeap#0 := $Heap;
                havoc $Heap;
                assume $IsGoodHeap($Heap);
                assume $oldHeap#0 == $Heap || $HeapSucc($oldHeap#0, $Heap);
                $_Frame#l0 := (lambda<alpha> $o: ref, $f: Field alpha :: 
                  $o != null && read($Heap, $o, alloc) ==> false);
                assume lambdaResult#0 == Mul(x#0, x#0);
                assume true;
                // CheckWellformedWithResult: any expression
                assume $Is(lambdaResult#0, TInt);
            }

            assume false;
        }

        // End Comprehension WF check
        ##n#0 := LitInt(0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#0, TInt, $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.from#canCall(LitInt(0));
        assume _module.Stream.Cons_q(Lit(_module.__default.from($LS($LZ), LitInt(0))));
        ##f#0 := Lit(AtLayer((lambda $l#7#ly#0: LayerType :: 
              Handle1((lambda $l#7#heap#0: Heap, $l#7#x#0: Box :: 
                  $Box(Mul($Unbox($l#7#x#0): int, $Unbox($l#7#x#0): int))), 
                (lambda $l#7#heap#0: Heap, $l#7#x#0: Box :: $IsBox($l#7#x#0, TInt)), 
                (lambda $l#7#heap#0: Heap, $l#7#x#0: Box :: 
                  SetRef_to_SetBox((lambda $l#7#o#0: ref :: false))))), 
            $LS($LZ)));
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#0, Tclass._System.___hTotalFunc1(TInt, TInt), $Heap);
        ##s#0 := Lit(_module.__default.from($LS($LZ), LitInt(0)));
        // assume allocatedness for argument to function
        assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Map#canCall(TInt, 
          TInt, 
          Lit(AtLayer((lambda $l#8#ly#0: LayerType :: 
                Handle1((lambda $l#8#heap#0: Heap, $l#8#x#0: Box :: 
                    $Box(Mul($Unbox($l#8#x#0): int, $Unbox($l#8#x#0): int))), 
                  (lambda $l#8#heap#0: Heap, $l#8#x#0: Box :: $IsBox($l#8#x#0, TInt)), 
                  (lambda $l#8#heap#0: Heap, $l#8#x#0: Box :: 
                    SetRef_to_SetBox((lambda $l#8#o#0: ref :: false))))), 
              $LS($LZ))), 
          Lit(_module.__default.from($LS($LZ), LitInt(0))));
        assume _module.Stream.Cons_q(Lit(_module.__default.Map(TInt, 
              TInt, 
              $LS($LZ), 
              Lit(AtLayer((lambda $l#9#ly#0: LayerType :: 
                    Handle1((lambda $l#9#heap#0: Heap, $l#9#x#0: Box :: 
                        $Box(Mul($Unbox($l#9#x#0): int, $Unbox($l#9#x#0): int))), 
                      (lambda $l#9#heap#0: Heap, $l#9#x#0: Box :: $IsBox($l#9#x#0, TInt)), 
                      (lambda $l#9#heap#0: Heap, $l#9#x#0: Box :: 
                        SetRef_to_SetBox((lambda $l#9#o#0: ref :: false))))), 
                  $LS($LZ))), 
              Lit(_module.__default.from($LS($LZ), LitInt(0))))));
        assume _module.__default.squares()
           == Lit(_module.__default.Map(TInt, 
              TInt, 
              $LS($LZ), 
              Lit(AtLayer((lambda $l#10#ly#0: LayerType :: 
                    Handle1((lambda $l#10#heap#0: Heap, $l#10#x#0: Box :: 
                        $Box(Mul($Unbox($l#10#x#0): int, $Unbox($l#10#x#0): int))), 
                      (lambda $l#10#heap#0: Heap, $l#10#x#0: Box :: $IsBox($l#10#x#0, TInt)), 
                      (lambda $l#10#heap#0: Heap, $l#10#x#0: Box :: 
                        SetRef_to_SetBox((lambda $l#10#o#0: ref :: false))))), 
                  $LS($LZ))), 
              Lit(_module.__default.from($LS($LZ), LitInt(0)))));
        assume _module.__default.from#canCall(LitInt(0))
           && _module.__default.Map#canCall(TInt, 
            TInt, 
            Lit(AtLayer((lambda $l#12#ly#0: LayerType :: 
                  Handle1((lambda $l#12#heap#0: Heap, $l#12#x#0: Box :: 
                      $Box(Mul($Unbox($l#12#x#0): int, $Unbox($l#12#x#0): int))), 
                    (lambda $l#12#heap#0: Heap, $l#12#x#0: Box :: $IsBox($l#12#x#0, TInt)), 
                    (lambda $l#12#heap#0: Heap, $l#12#x#0: Box :: 
                      SetRef_to_SetBox((lambda $l#12#o#0: ref :: false))))), 
                $LS($LZ))), 
            Lit(_module.__default.from($LS($LZ), LitInt(0))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.squares(), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for _module._default.take
function _module.__default.take(_module._default.take$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType)
   : DatatypeType;

function _module.__default.take#canCall(_module._default.take$_T0: Ty, n#0: int, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.take$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { _module.__default.take(_module._default.take$_T0, $LS($ly), n#0, s#0) } 
  _module.__default.take(_module._default.take$_T0, $LS($ly), n#0, s#0)
     == _module.__default.take(_module._default.take$_T0, $ly, n#0, s#0));

// fuel synonym axiom
axiom (forall _module._default.take$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { _module.__default.take(_module._default.take$_T0, AsFuelBottom($ly), n#0, s#0) } 
  _module.__default.take(_module._default.take$_T0, $ly, n#0, s#0)
     == _module.__default.take(_module._default.take$_T0, $LZ, n#0, s#0));

// consequence axiom for _module.__default.take
axiom 22 <= $FunctionContextHeight
   ==> (forall _module._default.take$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    { _module.__default.take(_module._default.take$_T0, $ly, n#0, s#0) } 
    _module.__default.take#canCall(_module._default.take$_T0, n#0, s#0)
         || (22 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(s#0, Tclass._module.Stream(_module._default.take$_T0)))
       ==> $Is(_module.__default.take(_module._default.take$_T0, $ly, n#0, s#0), 
        Tclass._module.List(_module._default.take$_T0)));

function _module.__default.take#requires(Ty, LayerType, int, DatatypeType) : bool;

// #requires axiom for _module.__default.take
axiom (forall _module._default.take$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { _module.__default.take#requires(_module._default.take$_T0, $ly, n#0, s#0) } 
  LitInt(0) <= n#0 && $Is(s#0, Tclass._module.Stream(_module._default.take$_T0))
     ==> _module.__default.take#requires(_module._default.take$_T0, $ly, n#0, s#0)
       == true);

// definition axiom for _module.__default.take (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall _module._default.take$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    { _module.__default.take(_module._default.take$_T0, $LS($ly), n#0, s#0) } 
    _module.__default.take#canCall(_module._default.take$_T0, n#0, s#0)
         || (22 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(s#0, Tclass._module.Stream(_module._default.take$_T0)))
       ==> (n#0 != LitInt(0)
           ==> _module.Stream.Cons_q(s#0)
             && 
            _module.Stream.Cons_q(s#0)
             && _module.__default.take#canCall(_module._default.take$_T0, n#0 - 1, _module.Stream.tail(s#0)))
         && _module.__default.take(_module._default.take$_T0, $LS($ly), n#0, s#0)
           == (if n#0 == LitInt(0)
             then #_module.List.Nil()
             else #_module.List.ListCons(_module.Stream.head(s#0), 
              _module.__default.take(_module._default.take$_T0, $ly, n#0 - 1, _module.Stream.tail(s#0)))));

// definition axiom for _module.__default.take for decreasing-related literals (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall _module._default.take$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.take(_module._default.take$_T0, $LS($ly), LitInt(n#0), s#0) } 
    _module.__default.take#canCall(_module._default.take$_T0, LitInt(n#0), s#0)
         || (22 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(s#0, Tclass._module.Stream(_module._default.take$_T0)))
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.Stream.Cons_q(s#0)
             && 
            _module.Stream.Cons_q(s#0)
             && _module.__default.take#canCall(_module._default.take$_T0, LitInt(n#0 - 1), _module.Stream.tail(s#0)))
         && _module.__default.take(_module._default.take$_T0, $LS($ly), LitInt(n#0), s#0)
           == (if LitInt(n#0) == LitInt(0)
             then #_module.List.Nil()
             else #_module.List.ListCons(_module.Stream.head(s#0), 
              _module.__default.take(_module._default.take$_T0, $LS($ly), LitInt(n#0 - 1), _module.Stream.tail(s#0)))));

// definition axiom for _module.__default.take for all literals (revealed)
axiom 22 <= $FunctionContextHeight
   ==> (forall _module._default.take$_T0: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.take(_module._default.take$_T0, $LS($ly), LitInt(n#0), Lit(s#0)) } 
    _module.__default.take#canCall(_module._default.take$_T0, LitInt(n#0), Lit(s#0))
         || (22 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(s#0, Tclass._module.Stream(_module._default.take$_T0)))
       ==> (LitInt(n#0) != LitInt(0)
           ==> _module.Stream.Cons_q(Lit(s#0))
             && 
            _module.Stream.Cons_q(Lit(s#0))
             && _module.__default.take#canCall(_module._default.take$_T0, LitInt(n#0 - 1), Lit(_module.Stream.tail(Lit(s#0)))))
         && _module.__default.take(_module._default.take$_T0, $LS($ly), LitInt(n#0), Lit(s#0))
           == (if LitInt(n#0) == LitInt(0)
             then #_module.List.Nil()
             else #_module.List.ListCons(Lit(_module.Stream.head(Lit(s#0))), 
              Lit(_module.__default.take(_module._default.take$_T0, 
                  $LS($ly), 
                  LitInt(n#0 - 1), 
                  Lit(_module.Stream.tail(Lit(s#0))))))));

procedure CheckWellformed$$_module.__default.take(_module._default.take$_T0: Ty, 
    n#0: int where LitInt(0) <= n#0, 
    s#0: DatatypeType
       where $Is(s#0, Tclass._module.Stream(_module._default.take$_T0)));
  free requires 22 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.take(_module._default.take$_T0: Ty, n#0: int, s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function take
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(74,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.take(_module._default.take$_T0, $LS($LZ), n#0, s#0), 
          Tclass._module.List(_module._default.take$_T0));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == LitInt(0))
        {
            assume _module.__default.take(_module._default.take$_T0, $LS($LZ), n#0, s#0)
               == Lit(#_module.List.Nil());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.take(_module._default.take$_T0, $LS($LZ), n#0, s#0), 
              Tclass._module.List(_module._default.take$_T0));
        }
        else
        {
            assume _module.Stream.Cons_q(s#0);
            assume _module.Stream.Cons_q(s#0);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##s#0 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.take$_T0), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.take#canCall(_module._default.take$_T0, n#0 - 1, _module.Stream.tail(s#0));
            assume _module.__default.take(_module._default.take$_T0, $LS($LZ), n#0, s#0)
               == #_module.List.ListCons(_module.Stream.head(s#0), 
                _module.__default.take(_module._default.take$_T0, $LS($LZ), n#0 - 1, _module.Stream.tail(s#0)));
            assume _module.Stream.Cons_q(s#0)
               && 
              _module.Stream.Cons_q(s#0)
               && _module.__default.take#canCall(_module._default.take$_T0, n#0 - 1, _module.Stream.tail(s#0));
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.take(_module._default.take$_T0, $LS($LZ), n#0, s#0), 
              Tclass._module.List(_module._default.take$_T0));
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.zip
function _module.__default.zip(_module._default.zip$T: Ty, 
    _module._default.zip$U: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
   : DatatypeType;

function _module.__default.zip#canCall(_module._default.zip$T: Ty, 
    _module._default.zip$U: Ty, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.zip$T: Ty, 
    _module._default.zip$U: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $LS($ly), a#0, b#0) } 
  _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $LS($ly), a#0, b#0)
     == _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $ly, a#0, b#0));

// fuel synonym axiom
axiom (forall _module._default.zip$T: Ty, 
    _module._default.zip$U: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.zip(_module._default.zip$T, _module._default.zip$U, AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $ly, a#0, b#0)
     == _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $LZ, a#0, b#0));

// consequence axiom for _module.__default.zip
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.zip$T: Ty, 
      _module._default.zip$U: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $ly, a#0, b#0) } 
    _module.__default.zip#canCall(_module._default.zip$T, _module._default.zip$U, a#0, b#0)
         || (24 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.Stream(_module._default.zip$T))
           && $Is(b#0, Tclass._module.Stream(_module._default.zip$U)))
       ==> $Is(_module.__default.zip(_module._default.zip$T, _module._default.zip$U, $ly, a#0, b#0), 
        Tclass._module.Stream(Tclass._System.Tuple2(_module._default.zip$T, _module._default.zip$U))));

function _module.__default.zip#requires(Ty, Ty, LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.zip
axiom (forall _module._default.zip$T: Ty, 
    _module._default.zip$U: Ty, 
    $ly: LayerType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.zip#requires(_module._default.zip$T, _module._default.zip$U, $ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.Stream(_module._default.zip$T))
       && $Is(b#0, Tclass._module.Stream(_module._default.zip$U))
     ==> _module.__default.zip#requires(_module._default.zip$T, _module._default.zip$U, $ly, a#0, b#0)
       == true);

// definition axiom for _module.__default.zip (revealed)
axiom 24 <= $FunctionContextHeight
   ==> (forall _module._default.zip$T: Ty, 
      _module._default.zip$U: Ty, 
      $ly: LayerType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $LS($ly), a#0, b#0) } 
    _module.__default.zip#canCall(_module._default.zip$T, _module._default.zip$U, a#0, b#0)
         || (24 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.Stream(_module._default.zip$T))
           && $Is(b#0, Tclass._module.Stream(_module._default.zip$U)))
       ==> _module.Stream.Cons_q(a#0)
         && _module.Stream.Cons_q(b#0)
         && 
        _module.Stream.Cons_q(a#0)
         && _module.Stream.Cons_q(b#0)
         && _module.__default.zip#canCall(_module._default.zip$T, 
          _module._default.zip$U, 
          _module.Stream.tail(a#0), 
          _module.Stream.tail(b#0))
         && _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $LS($ly), a#0, b#0)
           == #_module.Stream.Cons($Box(#_System._tuple#2._#Make2(_module.Stream.head(a#0), _module.Stream.head(b#0))), 
            _module.__default.zip(_module._default.zip$T, 
              _module._default.zip$U, 
              $ly, 
              _module.Stream.tail(a#0), 
              _module.Stream.tail(b#0))));

procedure {:abstemious} CheckWellformed$$_module.__default.zip(_module._default.zip$T: Ty, 
    _module._default.zip$U: Ty, 
    a#0: DatatypeType where $Is(a#0, Tclass._module.Stream(_module._default.zip$T)), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.Stream(_module._default.zip$U)));
  free requires 24 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:abstemious} CheckWellformed$$_module.__default.zip(_module._default.zip$T: Ty, 
    _module._default.zip$U: Ty, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function zip
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(79,30): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.zip(_module._default.zip$T, _module._default.zip$U, $LS($LZ), a#0, b#0), 
          Tclass._module.Stream(Tclass._System.Tuple2(_module._default.zip$T, _module._default.zip$U)));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(a#0);
        assume _module.Stream.Cons_q(b#0);
        assume _module.Stream.Cons_q(a#0);
        assume _module.Stream.Cons_q(b#0);
        ##a#0 := _module.Stream.tail(a#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, Tclass._module.Stream(_module._default.zip$T), $Heap);
        ##b#0 := _module.Stream.tail(b#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Stream(_module._default.zip$U), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.zip#canCall(_module._default.zip$T, 
          _module._default.zip$U, 
          _module.Stream.tail(a#0), 
          _module.Stream.tail(b#0));
        assume _module.Stream.Cons_q(_module.__default.zip(_module._default.zip$T, 
            _module._default.zip$U, 
            $LS($LZ), 
            _module.Stream.tail(a#0), 
            _module.Stream.tail(b#0)));
        assume _module.__default.zip(_module._default.zip$T, _module._default.zip$U, $LS($LZ), a#0, b#0)
           == #_module.Stream.Cons($Box(#_System._tuple#2._#Make2(_module.Stream.head(a#0), _module.Stream.head(b#0))), 
            _module.__default.zip(_module._default.zip$T, 
              _module._default.zip$U, 
              $LS($LZ), 
              _module.Stream.tail(a#0), 
              _module.Stream.tail(b#0)));
        assume _module.Stream.Cons_q(a#0)
           && _module.Stream.Cons_q(b#0)
           && 
          _module.Stream.Cons_q(a#0)
           && _module.Stream.Cons_q(b#0)
           && _module.__default.zip#canCall(_module._default.zip$T, 
            _module._default.zip$U, 
            _module.Stream.tail(a#0), 
            _module.Stream.tail(b#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.zip(_module._default.zip$T, _module._default.zip$U, $LS($LZ), a#0, b#0), 
          Tclass._module.Stream(Tclass._System.Tuple2(_module._default.zip$T, _module._default.zip$U)));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.addPair
function _module.__default.addPair($ly: LayerType, a#0: DatatypeType) : DatatypeType;

function _module.__default.addPair#canCall(a#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType :: 
  { _module.__default.addPair($LS($ly), a#0) } 
  _module.__default.addPair($LS($ly), a#0) == _module.__default.addPair($ly, a#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType :: 
  { _module.__default.addPair(AsFuelBottom($ly), a#0) } 
  _module.__default.addPair($ly, a#0) == _module.__default.addPair($LZ, a#0));

// consequence axiom for _module.__default.addPair
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType :: 
    { _module.__default.addPair($ly, a#0) } 
    _module.__default.addPair#canCall(a#0)
         || (25 != $FunctionContextHeight
           && $Is(a#0, Tclass._module.Stream(Tclass._System.Tuple2(TInt, TInt))))
       ==> $Is(_module.__default.addPair($ly, a#0), Tclass._module.Stream(TInt)));

function _module.__default.addPair#requires(LayerType, DatatypeType) : bool;

// #requires axiom for _module.__default.addPair
axiom (forall $ly: LayerType, a#0: DatatypeType :: 
  { _module.__default.addPair#requires($ly, a#0) } 
  $Is(a#0, Tclass._module.Stream(Tclass._System.Tuple2(TInt, TInt)))
     ==> _module.__default.addPair#requires($ly, a#0) == true);

// definition axiom for _module.__default.addPair (revealed)
axiom 25 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType :: 
    { _module.__default.addPair($LS($ly), a#0) } 
    _module.__default.addPair#canCall(a#0)
         || (25 != $FunctionContextHeight
           && $Is(a#0, Tclass._module.Stream(Tclass._System.Tuple2(TInt, TInt))))
       ==> _module.Stream.Cons_q(a#0)
         && _System.Tuple2.___hMake2_q($Unbox(_module.Stream.head(a#0)): DatatypeType)
         && 
        _module.Stream.Cons_q(a#0)
         && _System.Tuple2.___hMake2_q($Unbox(_module.Stream.head(a#0)): DatatypeType)
         && 
        _module.Stream.Cons_q(a#0)
         && _module.__default.addPair#canCall(_module.Stream.tail(a#0))
         && _module.__default.addPair($LS($ly), a#0)
           == #_module.Stream.Cons($Box($Unbox(_System.Tuple2._0($Unbox(_module.Stream.head(a#0)): DatatypeType)): int
                 + $Unbox(_System.Tuple2._1($Unbox(_module.Stream.head(a#0)): DatatypeType)): int), 
            _module.__default.addPair($ly, _module.Stream.tail(a#0))));

procedure {:abstemious} CheckWellformed$$_module.__default.addPair(a#0: DatatypeType
       where $Is(a#0, Tclass._module.Stream(Tclass._System.Tuple2(TInt, TInt))));
  free requires 25 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:abstemious} CheckWellformed$$_module.__default.addPair(a#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function addPair
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(84,30): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.addPair($LS($LZ), a#0), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(a#0);
        assume _System.Tuple2.___hMake2_q($Unbox(_module.Stream.head(a#0)): DatatypeType);
        assume _module.Stream.Cons_q(a#0);
        assume _System.Tuple2.___hMake2_q($Unbox(_module.Stream.head(a#0)): DatatypeType);
        assume _module.Stream.Cons_q(a#0);
        ##a#0 := _module.Stream.tail(a#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, Tclass._module.Stream(Tclass._System.Tuple2(TInt, TInt)), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.addPair#canCall(_module.Stream.tail(a#0));
        assume _module.Stream.Cons_q(_module.__default.addPair($LS($LZ), _module.Stream.tail(a#0)));
        assume _module.__default.addPair($LS($LZ), a#0)
           == #_module.Stream.Cons($Box($Unbox(_System.Tuple2._0($Unbox(_module.Stream.head(a#0)): DatatypeType)): int
                 + $Unbox(_System.Tuple2._1($Unbox(_module.Stream.head(a#0)): DatatypeType)): int), 
            _module.__default.addPair($LS($LZ), _module.Stream.tail(a#0)));
        assume _module.Stream.Cons_q(a#0)
           && _System.Tuple2.___hMake2_q($Unbox(_module.Stream.head(a#0)): DatatypeType)
           && 
          _module.Stream.Cons_q(a#0)
           && _System.Tuple2.___hMake2_q($Unbox(_module.Stream.head(a#0)): DatatypeType)
           && 
          _module.Stream.Cons_q(a#0)
           && _module.__default.addPair#canCall(_module.Stream.tail(a#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.addPair($LS($LZ), a#0), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.fib
function _module.__default.fib($ly: LayerType) : DatatypeType;

function _module.__default.fib#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.fib($LS($ly)) } 
  _module.__default.fib($LS($ly)) == _module.__default.fib($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.fib(AsFuelBottom($ly)) } 
  _module.__default.fib($ly) == _module.__default.fib($LZ));

// consequence axiom for _module.__default.fib
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.fib($ly) } 
    _module.__default.fib#canCall() || 26 != $FunctionContextHeight
       ==> $Is(_module.__default.fib($ly), Tclass._module.Stream(TInt)));

function _module.__default.fib#requires(LayerType) : bool;

// #requires axiom for _module.__default.fib
axiom (forall $ly: LayerType :: 
  { _module.__default.fib#requires($ly) } 
  _module.__default.fib#requires($ly) == true);

// definition axiom for _module.__default.fib (revealed)
axiom 26 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.fib($LS($ly)) } 
    _module.__default.fib#canCall() || 26 != $FunctionContextHeight
       ==> _module.__default.fib#canCall()
         && 
        _module.__default.fib#canCall()
         && _module.Stream.Cons_q(Lit(_module.__default.fib($ly)))
         && _module.__default.zip#canCall(TInt, 
          TInt, 
          Lit(_module.__default.fib($ly)), 
          Lit(_module.Stream.tail(Lit(_module.__default.fib($ly)))))
         && _module.__default.addPair#canCall(Lit(_module.__default.zip(TInt, 
              TInt, 
              $LS($LZ), 
              Lit(_module.__default.fib($ly)), 
              Lit(_module.Stream.tail(Lit(_module.__default.fib($ly)))))))
         && _module.__default.fib($LS($ly))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), 
              Lit(#_module.Stream.Cons($Box(LitInt(1)), 
                  Lit(_module.__default.addPair($LS($LZ), 
                      Lit(_module.__default.zip(TInt, 
                          TInt, 
                          $LS($LZ), 
                          Lit(_module.__default.fib($ly)), 
                          Lit(_module.Stream.tail(Lit(_module.__default.fib($ly)))))))))))));

procedure CheckWellformed$$_module.__default.fib();
  free requires 26 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.fib()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##a#1: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function fib
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(89,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.fib($LS($LZ)), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.fib#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.fib($LS($LZ))));
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.fib#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.fib($LS($LZ))));
        assume _module.Stream.Cons_q(Lit(_module.__default.fib($LS($LZ))));
        ##a#0 := Lit(_module.__default.fib($LS($LZ)));
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, Tclass._module.Stream(TInt), $Heap);
        ##b#0 := Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ)))));
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Stream(TInt), $Heap);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.zip#canCall(TInt, 
          TInt, 
          Lit(_module.__default.fib($LS($LZ))), 
          Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ))))));
        assume _module.Stream.Cons_q(Lit(_module.__default.zip(TInt, 
              TInt, 
              $LS($LZ), 
              Lit(_module.__default.fib($LS($LZ))), 
              Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ))))))));
        ##a#1 := Lit(_module.__default.zip(TInt, 
            TInt, 
            $LS($LZ), 
            Lit(_module.__default.fib($LS($LZ))), 
            Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ)))))));
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#1, Tclass._module.Stream(Tclass._System.Tuple2(TInt, TInt)), $Heap);
        b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.addPair#canCall(Lit(_module.__default.zip(TInt, 
              TInt, 
              $LS($LZ), 
              Lit(_module.__default.fib($LS($LZ))), 
              Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ))))))));
        assume _module.Stream.Cons_q(Lit(_module.__default.addPair($LS($LZ), 
              Lit(_module.__default.zip(TInt, 
                  TInt, 
                  $LS($LZ), 
                  Lit(_module.__default.fib($LS($LZ))), 
                  Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ))))))))));
        assume _module.__default.fib($LS($LZ))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), 
              Lit(#_module.Stream.Cons($Box(LitInt(1)), 
                  Lit(_module.__default.addPair($LS($LZ), 
                      Lit(_module.__default.zip(TInt, 
                          TInt, 
                          $LS($LZ), 
                          Lit(_module.__default.fib($LS($LZ))), 
                          Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ)))))))))))));
        assume _module.__default.fib#canCall()
           && 
          _module.__default.fib#canCall()
           && _module.Stream.Cons_q(Lit(_module.__default.fib($LS($LZ))))
           && _module.__default.zip#canCall(TInt, 
            TInt, 
            Lit(_module.__default.fib($LS($LZ))), 
            Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ))))))
           && _module.__default.addPair#canCall(Lit(_module.__default.zip(TInt, 
                TInt, 
                $LS($LZ), 
                Lit(_module.__default.fib($LS($LZ))), 
                Lit(_module.Stream.tail(Lit(_module.__default.fib($LS($LZ))))))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.fib($LS($LZ)), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for _module._default.add
function _module.__default.add($ly: LayerType, a#0: DatatypeType, b#0: DatatypeType) : DatatypeType;

function _module.__default.add#canCall(a#0: DatatypeType, b#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.add($LS($ly), a#0, b#0) } 
  _module.__default.add($LS($ly), a#0, b#0)
     == _module.__default.add($ly, a#0, b#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.add(AsFuelBottom($ly), a#0, b#0) } 
  _module.__default.add($ly, a#0, b#0) == _module.__default.add($LZ, a#0, b#0));

// consequence axiom for _module.__default.add
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.add($ly, a#0, b#0) } 
    _module.__default.add#canCall(a#0, b#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.Stream(TInt))
           && $Is(b#0, Tclass._module.Stream(TInt)))
       ==> $Is(_module.__default.add($ly, a#0, b#0), Tclass._module.Stream(TInt)));

function _module.__default.add#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.add
axiom (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
  { _module.__default.add#requires($ly, a#0, b#0) } 
  $Is(a#0, Tclass._module.Stream(TInt)) && $Is(b#0, Tclass._module.Stream(TInt))
     ==> _module.__default.add#requires($ly, a#0, b#0) == true);

// definition axiom for _module.__default.add (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, a#0: DatatypeType, b#0: DatatypeType :: 
    { _module.__default.add($LS($ly), a#0, b#0) } 
    _module.__default.add#canCall(a#0, b#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(a#0, Tclass._module.Stream(TInt))
           && $Is(b#0, Tclass._module.Stream(TInt)))
       ==> _module.Stream.Cons_q(a#0)
         && _module.Stream.Cons_q(b#0)
         && 
        _module.Stream.Cons_q(a#0)
         && _module.Stream.Cons_q(b#0)
         && _module.__default.add#canCall(_module.Stream.tail(a#0), _module.Stream.tail(b#0))
         && _module.__default.add($LS($ly), a#0, b#0)
           == #_module.Stream.Cons($Box($Unbox(_module.Stream.head(a#0)): int + $Unbox(_module.Stream.head(b#0)): int), 
            _module.__default.add($ly, _module.Stream.tail(a#0), _module.Stream.tail(b#0))));

procedure {:abstemious} CheckWellformed$$_module.__default.add(a#0: DatatypeType where $Is(a#0, Tclass._module.Stream(TInt)), 
    b#0: DatatypeType where $Is(b#0, Tclass._module.Stream(TInt)));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:abstemious} CheckWellformed$$_module.__default.add(a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function add
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(94,30): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.add($LS($LZ), a#0, b#0), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(a#0);
        assume _module.Stream.Cons_q(b#0);
        assume _module.Stream.Cons_q(a#0);
        assume _module.Stream.Cons_q(b#0);
        ##a#0 := _module.Stream.tail(a#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, Tclass._module.Stream(TInt), $Heap);
        ##b#0 := _module.Stream.tail(b#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Stream(TInt), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.add#canCall(_module.Stream.tail(a#0), _module.Stream.tail(b#0));
        assume _module.Stream.Cons_q(_module.__default.add($LS($LZ), _module.Stream.tail(a#0), _module.Stream.tail(b#0)));
        assume _module.__default.add($LS($LZ), a#0, b#0)
           == #_module.Stream.Cons($Box($Unbox(_module.Stream.head(a#0)): int + $Unbox(_module.Stream.head(b#0)): int), 
            _module.__default.add($LS($LZ), _module.Stream.tail(a#0), _module.Stream.tail(b#0)));
        assume _module.Stream.Cons_q(a#0)
           && _module.Stream.Cons_q(b#0)
           && 
          _module.Stream.Cons_q(a#0)
           && _module.Stream.Cons_q(b#0)
           && _module.__default.add#canCall(_module.Stream.tail(a#0), _module.Stream.tail(b#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.add($LS($LZ), a#0, b#0), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Fib
function _module.__default.Fib($ly: LayerType) : DatatypeType;

function _module.__default.Fib#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib($LS($ly)) } 
  _module.__default.Fib($LS($ly)) == _module.__default.Fib($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib(AsFuelBottom($ly)) } 
  _module.__default.Fib($ly) == _module.__default.Fib($LZ));

// consequence axiom for _module.__default.Fib
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.Fib($ly) } 
    _module.__default.Fib#canCall() || 27 != $FunctionContextHeight
       ==> $Is(_module.__default.Fib($ly), Tclass._module.Stream(TInt)));

function _module.__default.Fib#requires(LayerType) : bool;

// #requires axiom for _module.__default.Fib
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib#requires($ly) } 
  _module.__default.Fib#requires($ly) == true);

// definition axiom for _module.__default.Fib (revealed)
axiom 27 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.Fib($LS($ly)) } 
    _module.__default.Fib#canCall() || 27 != $FunctionContextHeight
       ==> _module.__default.Fib#canCall()
         && 
        _module.__default.Fib#canCall()
         && _module.Stream.Cons_q(Lit(_module.__default.Fib($ly)))
         && _module.__default.add#canCall(Lit(_module.__default.Fib($ly)), 
          Lit(_module.Stream.tail(Lit(_module.__default.Fib($ly)))))
         && _module.__default.Fib($LS($ly))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), 
              Lit(#_module.Stream.Cons($Box(LitInt(1)), 
                  Lit(_module.__default.add($LS($LZ), 
                      Lit(_module.__default.Fib($ly)), 
                      Lit(_module.Stream.tail(Lit(_module.__default.Fib($ly)))))))))));

procedure CheckWellformed$$_module.__default.Fib();
  free requires 27 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fib()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Fib
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(99,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Fib($LS($LZ)), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Fib#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Fib#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
        assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
        ##a#0 := Lit(_module.__default.Fib($LS($LZ)));
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, Tclass._module.Stream(TInt), $Heap);
        ##b#0 := Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))));
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Stream(TInt), $Heap);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.add#canCall(Lit(_module.__default.Fib($LS($LZ))), 
          Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))));
        assume _module.Stream.Cons_q(Lit(_module.__default.add($LS($LZ), 
              Lit(_module.__default.Fib($LS($LZ))), 
              Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))));
        assume _module.__default.Fib($LS($LZ))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), 
              Lit(#_module.Stream.Cons($Box(LitInt(1)), 
                  Lit(_module.__default.add($LS($LZ), 
                      Lit(_module.__default.Fib($LS($LZ))), 
                      Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))))))))));
        assume _module.__default.Fib#canCall()
           && 
          _module.__default.Fib#canCall()
           && _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))))
           && _module.__default.add#canCall(Lit(_module.__default.Fib($LS($LZ))), 
            Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Fib($LS($LZ)), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.Fib0
function _module.__default.Fib0($ly: LayerType) : DatatypeType;

function _module.__default.Fib0#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib0($LS($ly)) } 
  _module.__default.Fib0($LS($ly)) == _module.__default.Fib0($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib0(AsFuelBottom($ly)) } 
  _module.__default.Fib0($ly) == _module.__default.Fib0($LZ));

// consequence axiom for _module.__default.Fib0
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.Fib0($ly) } 
    _module.__default.Fib0#canCall() || 28 != $FunctionContextHeight
       ==> $Is(_module.__default.Fib0($ly), Tclass._module.Stream(TInt)));

function _module.__default.Fib0#requires(LayerType) : bool;

// #requires axiom for _module.__default.Fib0
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib0#requires($ly) } 
  _module.__default.Fib0#requires($ly) == true);

// definition axiom for _module.__default.Fib0 (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.Fib0($LS($ly)) } 
    _module.__default.Fib0#canCall() || 28 != $FunctionContextHeight
       ==> _module.__default.Fib1#canCall()
         && _module.__default.Fib0($LS($ly))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.Fib1($ly)))));

procedure CheckWellformed$$_module.__default.Fib0();
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fib0()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Fib0
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(104,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Fib0($LS($LZ)), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Fib1#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.Fib1($LS($LZ))));
        assume _module.__default.Fib0($LS($LZ))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.Fib1($LS($LZ)))));
        assume _module.__default.Fib1#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Fib0($LS($LZ)), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Fib1
function _module.__default.Fib1($ly: LayerType) : DatatypeType;

function _module.__default.Fib1#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib1($LS($ly)) } 
  _module.__default.Fib1($LS($ly)) == _module.__default.Fib1($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib1(AsFuelBottom($ly)) } 
  _module.__default.Fib1($ly) == _module.__default.Fib1($LZ));

// consequence axiom for _module.__default.Fib1
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.Fib1($ly) } 
    _module.__default.Fib1#canCall() || 28 != $FunctionContextHeight
       ==> $Is(_module.__default.Fib1($ly), Tclass._module.Stream(TInt)));

function _module.__default.Fib1#requires(LayerType) : bool;

// #requires axiom for _module.__default.Fib1
axiom (forall $ly: LayerType :: 
  { _module.__default.Fib1#requires($ly) } 
  _module.__default.Fib1#requires($ly) == true);

// definition axiom for _module.__default.Fib1 (revealed)
axiom 28 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.Fib1($LS($ly)) } 
    _module.__default.Fib1#canCall() || 28 != $FunctionContextHeight
       ==> _module.__default.Fib0#canCall()
         && _module.__default.Fib1#canCall()
         && _module.__default.add#canCall(Lit(_module.__default.Fib0($ly)), Lit(_module.__default.Fib1($ly)))
         && _module.__default.Fib1($LS($ly))
           == Lit(#_module.Stream.Cons($Box(LitInt(1)), 
              Lit(_module.__default.add($LS($LZ), Lit(_module.__default.Fib0($ly)), Lit(_module.__default.Fib1($ly)))))));

procedure CheckWellformed$$_module.__default.Fib1();
  free requires 28 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Fib1()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var b$reqreads#2: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;

    // AddWellformednessCheck for function Fib1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(109,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Fib1($LS($LZ)), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Fib0#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.Fib0($LS($LZ))));
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Fib1#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.Fib1($LS($LZ))));
        ##a#0 := Lit(_module.__default.Fib0($LS($LZ)));
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, Tclass._module.Stream(TInt), $Heap);
        ##b#0 := Lit(_module.__default.Fib1($LS($LZ)));
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Stream(TInt), $Heap);
        b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.add#canCall(Lit(_module.__default.Fib0($LS($LZ))), Lit(_module.__default.Fib1($LS($LZ))));
        assume _module.Stream.Cons_q(Lit(_module.__default.add($LS($LZ), 
              Lit(_module.__default.Fib0($LS($LZ))), 
              Lit(_module.__default.Fib1($LS($LZ))))));
        assume _module.__default.Fib1($LS($LZ))
           == Lit(#_module.Stream.Cons($Box(LitInt(1)), 
              Lit(_module.__default.add($LS($LZ), 
                  Lit(_module.__default.Fib0($LS($LZ))), 
                  Lit(_module.__default.Fib1($LS($LZ)))))));
        assume _module.__default.Fib0#canCall()
           && _module.__default.Fib1#canCall()
           && _module.__default.add#canCall(Lit(_module.__default.Fib0($LS($LZ))), Lit(_module.__default.Fib1($LS($LZ))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Fib1($LS($LZ)), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
        assert b$reqreads#1;
        assert b$reqreads#2;
    }
}



// function declaration for _module._default.OhOnes
function _module.__default.OhOnes($ly: LayerType) : DatatypeType;

function _module.__default.OhOnes#canCall() : bool;

// layer synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.OhOnes($LS($ly)) } 
  _module.__default.OhOnes($LS($ly)) == _module.__default.OhOnes($ly));

// fuel synonym axiom
axiom (forall $ly: LayerType :: 
  { _module.__default.OhOnes(AsFuelBottom($ly)) } 
  _module.__default.OhOnes($ly) == _module.__default.OhOnes($LZ));

// consequence axiom for _module.__default.OhOnes
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.OhOnes($ly) } 
    _module.__default.OhOnes#canCall() || 1 != $FunctionContextHeight
       ==> $Is(_module.__default.OhOnes($ly), Tclass._module.Stream(TInt)));

function _module.__default.OhOnes#requires(LayerType) : bool;

// #requires axiom for _module.__default.OhOnes
axiom (forall $ly: LayerType :: 
  { _module.__default.OhOnes#requires($ly) } 
  _module.__default.OhOnes#requires($ly) == true);

// definition axiom for _module.__default.OhOnes (revealed)
axiom 1 <= $FunctionContextHeight
   ==> (forall $ly: LayerType :: 
    { _module.__default.OhOnes($LS($ly)) } 
    _module.__default.OhOnes#canCall() || 1 != $FunctionContextHeight
       ==> _module.__default.OhOnes#canCall()
         && _module.Stream.Cons_q(Lit(_module.__default.OhOnes($ly)))
         && _module.__default.OhOnes($LS($ly))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), 
              Lit(#_module.Stream.Cons($Box(LitInt(1)), Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($ly)))))))));

procedure CheckWellformed$$_module.__default.OhOnes();
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.OhOnes()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function OhOnes
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(114,16): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.OhOnes($LS($LZ)), Tclass._module.Stream(TInt));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.OhOnes#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LZ))));
        assume _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LZ))));
        assume _module.__default.OhOnes($LS($LZ))
           == Lit(#_module.Stream.Cons($Box(LitInt(0)), 
              Lit(#_module.Stream.Cons($Box(LitInt(1)), 
                  Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LZ)))))))));
        assume _module.__default.OhOnes#canCall()
           && _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LZ))));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.OhOnes($LS($LZ)), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.Combine
function _module.__default.Combine(_module._default.Combine$T: Ty, 
    $ly: LayerType, 
    f#0: HandleType, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
   : DatatypeType;

function _module.__default.Combine#canCall(_module._default.Combine$T: Ty, 
    f#0: HandleType, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
   : bool;

// layer synonym axiom
axiom (forall _module._default.Combine$T: Ty, 
    $ly: LayerType, 
    f#0: HandleType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Combine(_module._default.Combine$T, $LS($ly), f#0, a#0, b#0) } 
  _module.__default.Combine(_module._default.Combine$T, $LS($ly), f#0, a#0, b#0)
     == _module.__default.Combine(_module._default.Combine$T, $ly, f#0, a#0, b#0));

// fuel synonym axiom
axiom (forall _module._default.Combine$T: Ty, 
    $ly: LayerType, 
    f#0: HandleType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Combine(_module._default.Combine$T, AsFuelBottom($ly), f#0, a#0, b#0) } 
  _module.__default.Combine(_module._default.Combine$T, $ly, f#0, a#0, b#0)
     == _module.__default.Combine(_module._default.Combine$T, $LZ, f#0, a#0, b#0));

// consequence axiom for _module.__default.Combine
axiom 8 <= $FunctionContextHeight
   ==> (forall _module._default.Combine$T: Ty, 
      $ly: LayerType, 
      f#0: HandleType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.Combine(_module._default.Combine$T, $ly, f#0, a#0, b#0) } 
    _module.__default.Combine#canCall(_module._default.Combine$T, f#0, a#0, b#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(f#0, 
            Tclass._System.___hTotalFunc2(_module._default.Combine$T, 
              _module._default.Combine$T, 
              _module._default.Combine$T))
           && $Is(a#0, Tclass._module.Stream(_module._default.Combine$T))
           && $Is(b#0, Tclass._module.Stream(_module._default.Combine$T)))
       ==> $Is(_module.__default.Combine(_module._default.Combine$T, $ly, f#0, a#0, b#0), 
        Tclass._module.Stream(_module._default.Combine$T)));

function _module.__default.Combine#requires(Ty, LayerType, HandleType, DatatypeType, DatatypeType) : bool;

// #requires axiom for _module.__default.Combine
axiom (forall _module._default.Combine$T: Ty, 
    $ly: LayerType, 
    $Heap: Heap, 
    f#0: HandleType, 
    a#0: DatatypeType, 
    b#0: DatatypeType :: 
  { _module.__default.Combine#requires(_module._default.Combine$T, $ly, f#0, a#0, b#0), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && $Is(f#0, 
        Tclass._System.___hTotalFunc2(_module._default.Combine$T, 
          _module._default.Combine$T, 
          _module._default.Combine$T))
       && $Is(a#0, Tclass._module.Stream(_module._default.Combine$T))
       && $Is(b#0, Tclass._module.Stream(_module._default.Combine$T))
     ==> _module.__default.Combine#requires(_module._default.Combine$T, $ly, f#0, a#0, b#0)
       == true);

// definition axiom for _module.__default.Combine (revealed)
axiom 8 <= $FunctionContextHeight
   ==> (forall _module._default.Combine$T: Ty, 
      $ly: LayerType, 
      $Heap: Heap, 
      f#0: HandleType, 
      a#0: DatatypeType, 
      b#0: DatatypeType :: 
    { _module.__default.Combine(_module._default.Combine$T, $LS($ly), f#0, a#0, b#0), $IsGoodHeap($Heap) } 
    _module.__default.Combine#canCall(_module._default.Combine$T, f#0, a#0, b#0)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && $Is(f#0, 
            Tclass._System.___hTotalFunc2(_module._default.Combine$T, 
              _module._default.Combine$T, 
              _module._default.Combine$T))
           && $Is(a#0, Tclass._module.Stream(_module._default.Combine$T))
           && $Is(b#0, Tclass._module.Stream(_module._default.Combine$T)))
       ==> _module.Stream.Cons_q(a#0)
         && _module.Stream.Cons_q(b#0)
         && 
        _module.Stream.Cons_q(a#0)
         && _module.Stream.Cons_q(b#0)
         && _module.__default.Combine#canCall(_module._default.Combine$T, 
          f#0, 
          _module.Stream.tail(a#0), 
          _module.Stream.tail(b#0))
         && _module.__default.Combine(_module._default.Combine$T, $LS($ly), f#0, a#0, b#0)
           == #_module.Stream.Cons(Apply2(_module._default.Combine$T, 
              _module._default.Combine$T, 
              _module._default.Combine$T, 
              $Heap, 
              f#0, 
              _module.Stream.head(a#0), 
              _module.Stream.head(b#0)), 
            _module.__default.Combine(_module._default.Combine$T, 
              $ly, 
              f#0, 
              _module.Stream.tail(a#0), 
              _module.Stream.tail(b#0))));

procedure {:abstemious} CheckWellformed$$_module.__default.Combine(_module._default.Combine$T: Ty, 
    f#0: HandleType
       where $Is(f#0, 
        Tclass._System.___hTotalFunc2(_module._default.Combine$T, 
          _module._default.Combine$T, 
          _module._default.Combine$T)), 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.Stream(_module._default.Combine$T)), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.Stream(_module._default.Combine$T)));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:abstemious} CheckWellformed$$_module.__default.Combine(_module._default.Combine$T: Ty, 
    f#0: HandleType, 
    a#0: DatatypeType, 
    b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##f#0: HandleType;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Combine
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(120,2): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.Combine(_module._default.Combine$T, $LS($LZ), f#0, a#0, b#0), 
          Tclass._module.Stream(_module._default.Combine$T));
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assume _module.Stream.Cons_q(a#0);
        assume _module.Stream.Cons_q(b#0);
        assume _module.Stream.Cons_q(a#0);
        assume _module.Stream.Cons_q(b#0);
        ##f#0 := f#0;
        // assume allocatedness for argument to function
        assume $IsAlloc(##f#0, 
          Tclass._System.___hTotalFunc2(_module._default.Combine$T, 
            _module._default.Combine$T, 
            _module._default.Combine$T), 
          $Heap);
        ##a#0 := _module.Stream.tail(a#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##a#0, Tclass._module.Stream(_module._default.Combine$T), $Heap);
        ##b#0 := _module.Stream.tail(b#0);
        // assume allocatedness for argument to function
        assume $IsAlloc(##b#0, Tclass._module.Stream(_module._default.Combine$T), $Heap);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.Combine#canCall(_module._default.Combine$T, 
          f#0, 
          _module.Stream.tail(a#0), 
          _module.Stream.tail(b#0));
        assume _module.Stream.Cons_q(_module.__default.Combine(_module._default.Combine$T, 
            $LS($LZ), 
            f#0, 
            _module.Stream.tail(a#0), 
            _module.Stream.tail(b#0)));
        assume _module.__default.Combine(_module._default.Combine$T, $LS($LZ), f#0, a#0, b#0)
           == #_module.Stream.Cons(Apply2(_module._default.Combine$T, 
              _module._default.Combine$T, 
              _module._default.Combine$T, 
              $Heap, 
              f#0, 
              _module.Stream.head(a#0), 
              _module.Stream.head(b#0)), 
            _module.__default.Combine(_module._default.Combine$T, 
              $LS($LZ), 
              f#0, 
              _module.Stream.tail(a#0), 
              _module.Stream.tail(b#0)));
        assume _module.Stream.Cons_q(a#0)
           && _module.Stream.Cons_q(b#0)
           && 
          _module.Stream.Cons_q(a#0)
           && _module.Stream.Cons_q(b#0)
           && _module.__default.Combine#canCall(_module._default.Combine$T, 
            f#0, 
            _module.Stream.tail(a#0), 
            _module.Stream.tail(b#0));
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.Combine(_module._default.Combine$T, $LS($LZ), f#0, a#0, b#0), 
          Tclass._module.Stream(_module._default.Combine$T));
        assert b$reqreads#0;
    }
}



// function declaration for _module._default.nth
function _module.__default.nth(_module._default.nth$T: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType) : Box;

function _module.__default.nth#canCall(_module._default.nth$T: Ty, n#0: int, s#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall _module._default.nth$T: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { _module.__default.nth(_module._default.nth$T, $LS($ly), n#0, s#0) } 
  _module.__default.nth(_module._default.nth$T, $LS($ly), n#0, s#0)
     == _module.__default.nth(_module._default.nth$T, $ly, n#0, s#0));

// fuel synonym axiom
axiom (forall _module._default.nth$T: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { _module.__default.nth(_module._default.nth$T, AsFuelBottom($ly), n#0, s#0) } 
  _module.__default.nth(_module._default.nth$T, $ly, n#0, s#0)
     == _module.__default.nth(_module._default.nth$T, $LZ, n#0, s#0));

// consequence axiom for _module.__default.nth
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.nth$T: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    { _module.__default.nth(_module._default.nth$T, $ly, n#0, s#0) } 
    _module.__default.nth#canCall(_module._default.nth$T, n#0, s#0)
         || (29 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(s#0, Tclass._module.Stream(_module._default.nth$T)))
       ==> $IsBox(_module.__default.nth(_module._default.nth$T, $ly, n#0, s#0), 
        _module._default.nth$T));

function _module.__default.nth#requires(Ty, LayerType, int, DatatypeType) : bool;

// #requires axiom for _module.__default.nth
axiom (forall _module._default.nth$T: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
  { _module.__default.nth#requires(_module._default.nth$T, $ly, n#0, s#0) } 
  LitInt(0) <= n#0 && $Is(s#0, Tclass._module.Stream(_module._default.nth$T))
     ==> _module.__default.nth#requires(_module._default.nth$T, $ly, n#0, s#0) == true);

// definition axiom for _module.__default.nth (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.nth$T: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    { _module.__default.nth(_module._default.nth$T, $LS($ly), n#0, s#0) } 
    _module.__default.nth#canCall(_module._default.nth$T, n#0, s#0)
         || (29 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(s#0, Tclass._module.Stream(_module._default.nth$T)))
       ==> (n#0 == LitInt(0) ==> _module.Stream.Cons_q(s#0))
         && (n#0 != LitInt(0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.nth#canCall(_module._default.nth$T, n#0 - 1, _module.Stream.tail(s#0)))
         && _module.__default.nth(_module._default.nth$T, $LS($ly), n#0, s#0)
           == (if n#0 == LitInt(0)
             then _module.Stream.head(s#0)
             else _module.__default.nth(_module._default.nth$T, $ly, n#0 - 1, _module.Stream.tail(s#0))));

// definition axiom for _module.__default.nth for decreasing-related literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.nth$T: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.nth(_module._default.nth$T, $LS($ly), LitInt(n#0), s#0) } 
    _module.__default.nth#canCall(_module._default.nth$T, LitInt(n#0), s#0)
         || (29 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(s#0, Tclass._module.Stream(_module._default.nth$T)))
       ==> (LitInt(n#0) == LitInt(0) ==> _module.Stream.Cons_q(s#0))
         && (LitInt(n#0) != LitInt(0)
           ==> _module.Stream.Cons_q(s#0)
             && _module.__default.nth#canCall(_module._default.nth$T, LitInt(n#0 - 1), _module.Stream.tail(s#0)))
         && _module.__default.nth(_module._default.nth$T, $LS($ly), LitInt(n#0), s#0)
           == (if LitInt(n#0) == LitInt(0)
             then _module.Stream.head(s#0)
             else _module.__default.nth(_module._default.nth$T, $LS($ly), LitInt(n#0 - 1), _module.Stream.tail(s#0))));

// definition axiom for _module.__default.nth for all literals (revealed)
axiom 29 <= $FunctionContextHeight
   ==> (forall _module._default.nth$T: Ty, $ly: LayerType, n#0: int, s#0: DatatypeType :: 
    {:weight 3} { _module.__default.nth(_module._default.nth$T, $LS($ly), LitInt(n#0), Lit(s#0)) } 
    _module.__default.nth#canCall(_module._default.nth$T, LitInt(n#0), Lit(s#0))
         || (29 != $FunctionContextHeight
           && 
          LitInt(0) <= n#0
           && $Is(s#0, Tclass._module.Stream(_module._default.nth$T)))
       ==> (LitInt(n#0) == LitInt(0) ==> _module.Stream.Cons_q(Lit(s#0)))
         && (LitInt(n#0) != LitInt(0)
           ==> _module.Stream.Cons_q(Lit(s#0))
             && _module.__default.nth#canCall(_module._default.nth$T, LitInt(n#0 - 1), Lit(_module.Stream.tail(Lit(s#0)))))
         && _module.__default.nth(_module._default.nth$T, $LS($ly), LitInt(n#0), Lit(s#0))
           == (if LitInt(n#0) == LitInt(0)
             then _module.Stream.head(Lit(s#0))
             else _module.__default.nth(_module._default.nth$T, 
              $LS($ly), 
              LitInt(n#0 - 1), 
              Lit(_module.Stream.tail(Lit(s#0))))));

procedure CheckWellformed$$_module.__default.nth(_module._default.nth$T: Ty, 
    n#0: int where LitInt(0) <= n#0, 
    s#0: DatatypeType where $Is(s#0, Tclass._module.Stream(_module._default.nth$T)));
  free requires 29 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.nth(_module._default.nth$T: Ty, n#0: int, s#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##s#0: DatatypeType;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function nth
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(127,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $IsBox(_module.__default.nth(_module._default.nth$T, $LS($LZ), n#0, s#0), 
          _module._default.nth$T);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 == LitInt(0))
        {
            assume _module.Stream.Cons_q(s#0);
            assume _module.__default.nth(_module._default.nth$T, $LS($LZ), n#0, s#0)
               == _module.Stream.head(s#0);
            assume _module.Stream.Cons_q(s#0);
            // CheckWellformedWithResult: any expression
            assume $IsBox(_module.__default.nth(_module._default.nth$T, $LS($LZ), n#0, s#0), 
              _module._default.nth$T);
        }
        else
        {
            assume _module.Stream.Cons_q(s#0);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#0 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            ##s#0 := _module.Stream.tail(s#0);
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#0, Tclass._module.Stream(_module._default.nth$T), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.nth#canCall(_module._default.nth$T, n#0 - 1, _module.Stream.tail(s#0));
            assume _module.__default.nth(_module._default.nth$T, $LS($LZ), n#0, s#0)
               == _module.__default.nth(_module._default.nth$T, $LS($LZ), n#0 - 1, _module.Stream.tail(s#0));
            assume _module.Stream.Cons_q(s#0)
               && _module.__default.nth#canCall(_module._default.nth$T, n#0 - 1, _module.Stream.tail(s#0));
            // CheckWellformedWithResult: any expression
            assume $IsBox(_module.__default.nth(_module._default.nth$T, $LS($LZ), n#0, s#0), 
              _module._default.nth$T);
        }

        assert b$reqreads#0;
    }
}



// function declaration for _module._default.nfib
function _module.__default.nfib($ly: LayerType, n#0: int) : int;

function _module.__default.nfib#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.nfib($LS($ly), n#0) } 
  _module.__default.nfib($LS($ly), n#0) == _module.__default.nfib($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.nfib(AsFuelBottom($ly), n#0) } 
  _module.__default.nfib($ly, n#0) == _module.__default.nfib($LZ, n#0));

// consequence axiom for _module.__default.nfib
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.nfib($ly, n#0) } 
    _module.__default.nfib#canCall(n#0)
         || (30 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> LitInt(0) <= _module.__default.nfib($ly, n#0));

function _module.__default.nfib#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.nfib
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.nfib#requires($ly, n#0) } 
  LitInt(0) <= n#0 ==> _module.__default.nfib#requires($ly, n#0) == true);

// definition axiom for _module.__default.nfib (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.nfib($LS($ly), n#0) } 
    _module.__default.nfib#canCall(n#0)
         || (30 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (2 <= n#0
           ==> _module.__default.nfib#canCall(n#0 - 2)
             && _module.__default.nfib#canCall(n#0 - 1))
         && _module.__default.nfib($LS($ly), n#0)
           == (if n#0 < 2
             then n#0
             else _module.__default.nfib($ly, n#0 - 2) + _module.__default.nfib($ly, n#0 - 1)));

// definition axiom for _module.__default.nfib for all literals (revealed)
axiom 30 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    {:weight 3} { _module.__default.nfib($LS($ly), LitInt(n#0)) } 
    _module.__default.nfib#canCall(LitInt(n#0))
         || (30 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> (!Lit(n#0 < 2)
           ==> _module.__default.nfib#canCall(LitInt(n#0 - 2))
             && _module.__default.nfib#canCall(LitInt(n#0 - 1)))
         && _module.__default.nfib($LS($ly), LitInt(n#0))
           == (if n#0 < 2
             then n#0
             else _module.__default.nfib($LS($ly), LitInt(n#0 - 2))
               + _module.__default.nfib($LS($ly), LitInt(n#0 - 1))));

procedure CheckWellformed$$_module.__default.nfib(n#0: int where LitInt(0) <= n#0);
  free requires 30 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.nfib(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##n#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function nfib
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(132,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume LitInt(0) <= _module.__default.nfib($LS($LZ), n#0);
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (n#0 < 2)
        {
            assume _module.__default.nfib($LS($LZ), n#0) == n#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.nfib($LS($LZ), n#0), Tclass._System.nat());
        }
        else
        {
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#0 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
            b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#0 == n#0;
            assert ##n#0 < n#0;
            assume _module.__default.nfib#canCall(n#0 - 2);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#1 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
            b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || ##n#1 == n#0;
            assert ##n#1 < n#0;
            assume _module.__default.nfib#canCall(n#0 - 1);
            assert $Is(_module.__default.nfib($LS($LZ), n#0 - 2)
                 + _module.__default.nfib($LS($LZ), n#0 - 1), 
              Tclass._System.nat());
            assume _module.__default.nfib($LS($LZ), n#0)
               == _module.__default.nfib($LS($LZ), n#0 - 2)
                 + _module.__default.nfib($LS($LZ), n#0 - 1);
            assume _module.__default.nfib#canCall(n#0 - 2)
               && _module.__default.nfib#canCall(n#0 - 1);
            // CheckWellformedWithResult: any expression
            assume $Is(_module.__default.nfib($LS($LZ), n#0), Tclass._System.nat());
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.Ones__Correct(n#0: int where LitInt(0) <= n#0);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.Ones__Correct(n#0: int where LitInt(0) <= n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ones#canCall()
     && _module.__default.nth#canCall(TInt, n#0, Lit(_module.__default.ones($LS($LZ))));
  ensures $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, Lit(_module.__default.ones($LS($LS($LZ)))))): int
     == LitInt(1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.Ones__Correct(n#0: int where LitInt(0) <= n#0) returns ($_reverifyPost: bool);
  free requires 31 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ones#canCall()
     && _module.__default.nth#canCall(TInt, n#0, Lit(_module.__default.ones($LS($LZ))));
  ensures $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, Lit(_module.__default.ones($LS($LS($LZ)))))): int
     == LitInt(1);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.Ones__Correct(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: Ones_Correct, Impl$$_module.__default.Ones__Correct
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(139,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: int :: 
      LitInt(0) <= $ih#n0#0 && Lit(true) && 0 <= $ih#n0#0 && $ih#n0#0 < n#0
         ==> $Unbox(_module.__default.nth(TInt, $LS($LZ), $ih#n0#0, Lit(_module.__default.ones($LS($LZ))))): int
           == LitInt(1));
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.OhOnesTail__Correct();
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.OhOnesTail__Correct();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LZ))))))
     && $IsA#_module.Stream(Lit(_module.__default.ones($LS($LZ))))
     && 
    _module.__default.OhOnes#canCall()
     && _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LZ))))
     && _module.__default.ones#canCall();
  ensures $Eq#_module.Stream(TInt, 
    TInt, 
    $LS($LS($LZ)), 
    _module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ))))), 
    _module.__default.ones($LS($LS($LZ))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} CoCall$$_module.__default.OhOnesTail__Correct_h(_k#0: Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.OhOnes#canCall()
     && _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LZ))))
     && _module.__default.ones#canCall();
  free ensures $PrefixEq#_module.Stream(TInt, 
    TInt, 
    _k#0, 
    $LS($LS($LZ)), 
    Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LZ))))), 
    Lit(_module.__default.ones($LS($LZ))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} Impl$$_module.__default.OhOnesTail__Correct_h(_k#0: Box) returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.OhOnes#canCall()
     && _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LZ))))
     && _module.__default.ones#canCall();
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LZ))))), 
      Lit(_module.__default.ones($LS($LZ))))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ)))))))
       ==> _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LS($LZ)))))
         && 
        $Unbox(_module.Stream.head(Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ)))))))): int
           == $Unbox(_module.Stream.head(Lit(_module.__default.ones($LS($LS($LZ)))))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ))))))), 
          _module.Stream.tail(Lit(_module.__default.ones($LS($LS($LZ)))))));
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LZ))))), 
      Lit(_module.__default.ones($LS($LZ))))
     || 
    (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ)))))))
       ==> _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LS($LZ)))))
         && 
        $Unbox(_module.Stream.head(Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ)))))))): int
           == $Unbox(_module.Stream.head(Lit(_module.__default.ones($LS($LS($LZ)))))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ))))))), 
          _module.Stream.tail(Lit(_module.__default.ones($LS($LS($LZ)))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(TInt, 
        TInt, 
        $LS($LS($LZ)), 
        Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LZ))))), 
        Lit(_module.__default.ones($LS($LZ)))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0} Impl$$_module.__default.OhOnesTail__Correct_h(_k#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: OhOnesTail_Correct#, Impl$$_module.__default.OhOnesTail__Correct_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(142,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box :: 
      Lit(true) && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(TInt, 
          TInt, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LZ))))), 
          Lit(_module.__default.ones($LS($LZ)))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(144,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(142,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box :: 
          ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(TInt, 
              TInt, 
              _k'#0, 
              $LS($LS($LZ)), 
              Lit(_module.Stream.tail(Lit(_module.__default.OhOnes($LS($LZ))))), 
              Lit(_module.__default.ones($LS($LZ)))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(142,15)"} true;
    }
}



procedure CheckWellformed$$_module.__default.OhOnes__Correct();
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.OhOnes__Correct();
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(Lit(_module.__default.OhOnes($LS($LZ))))
     && 
    _module.__default.OhOnes#canCall()
     && _module.__default.ones#canCall();
  ensures $Eq#_module.Stream(TInt, 
    TInt, 
    $LS($LS($LZ)), 
    _module.__default.OhOnes($LS($LS($LZ))), 
    #_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LS($LZ))))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} CoCall$$_module.__default.OhOnes__Correct_h(_k#0: Box);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.OhOnes#canCall() && _module.__default.ones#canCall();
  free ensures $PrefixEq#_module.Stream(TInt, 
    TInt, 
    _k#0, 
    $LS($LS($LZ)), 
    Lit(_module.__default.OhOnes($LS($LZ))), 
    Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LZ))))));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0} Impl$$_module.__default.OhOnes__Correct_h(_k#0: Box) returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.OhOnes#canCall() && _module.__default.ones#canCall();
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      Lit(_module.__default.OhOnes($LS($LZ))), 
      Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LZ))))))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LS($LZ)))))
       ==> _module.Stream.Cons_q(Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LS($LZ)))))))
         && 
        $Unbox(_module.Stream.head(Lit(_module.__default.OhOnes($LS($LS($LZ)))))): int
           == $Unbox(_module.Stream.head(Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LS($LZ)))))))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ))))), 
          _module.Stream.tail(Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LS($LZ)))))))));
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      Lit(_module.__default.OhOnes($LS($LZ))), 
      Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LZ))))))
     || 
    (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(Lit(_module.__default.OhOnes($LS($LS($LZ)))))
       ==> _module.Stream.Cons_q(Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LS($LZ)))))))
         && 
        $Unbox(_module.Stream.head(Lit(_module.__default.OhOnes($LS($LS($LZ)))))): int
           == $Unbox(_module.Stream.head(Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LS($LZ)))))))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(Lit(_module.__default.OhOnes($LS($LS($LZ))))), 
          _module.Stream.tail(Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LS($LZ)))))))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(TInt, 
        TInt, 
        $LS($LS($LZ)), 
        Lit(_module.__default.OhOnes($LS($LZ))), 
        Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LZ)))))));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0} Impl$$_module.__default.OhOnes__Correct_h(_k#0: Box) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: OhOnes_Correct#, Impl$$_module.__default.OhOnes__Correct_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(147,15): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box :: 
      Lit(true) && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(TInt, 
          TInt, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          Lit(_module.__default.OhOnes($LS($LZ))), 
          Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LZ)))))));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(149,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(147,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box :: 
          ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(TInt, 
              TInt, 
              _k'#0, 
              $LS($LS($LZ)), 
              Lit(_module.__default.OhOnes($LS($LZ))), 
              Lit(#_module.Stream.Cons($Box(LitInt(0)), Lit(_module.__default.ones($LS($LZ)))))));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(147,15)"} true;
    }
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.OhOnes__Correct_k(n#0: int where LitInt(0) <= n#0);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.OhOnes__Correct_k(n#0: int where LitInt(0) <= n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.OhOnes#canCall()
     && _module.__default.nth#canCall(TInt, n#0, Lit(_module.__default.OhOnes($LS($LZ))));
  ensures $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, Lit(_module.__default.OhOnes($LS($LS($LZ)))))): int
     == (if n#0 == LitInt(0) then 0 else 1);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.OhOnes__Correct_k(n#0: int where LitInt(0) <= n#0) returns ($_reverifyPost: bool);
  free requires 32 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.OhOnes#canCall()
     && _module.__default.nth#canCall(TInt, n#0, Lit(_module.__default.OhOnes($LS($LZ))));
  ensures $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, Lit(_module.__default.OhOnes($LS($LS($LZ)))))): int
     == (if n#0 == LitInt(0) then 0 else 1);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.OhOnes__Correct_k(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var n##0_0: int;

    // AddMethodImpl: OhOnes_Correct', Impl$$_module.__default.OhOnes__Correct_k
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(154,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: int :: 
      LitInt(0) <= $ih#n0#0 && Lit(true) && 0 <= $ih#n0#0 && $ih#n0#0 < n#0
         ==> $Unbox(_module.__default.nth(TInt, $LS($LZ), $ih#n0#0, Lit(_module.__default.OhOnes($LS($LZ))))): int
           == (if $ih#n0#0 == LitInt(0) then 0 else 1));
    $_reverifyPost := false;
    // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(155,17)
    // TrCallStmt: Before ProcessCallStmt
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call Call$$_module.__default.OhOnes__Correct();
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(155,18)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(156,3)
    assume true;
    if (n#0 != 0)
    {
        // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(157,17)
        // TrCallStmt: Before ProcessCallStmt
        assume true;
        // ProcessCallStmt: CheckSubrange
        assert $Is(n#0 - 1, Tclass._System.nat());
        n##0_0 := n#0 - 1;
        assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        // ProcessCallStmt: Make the call
        call Call$$_module.__default.Ones__Correct(n##0_0);
        // TrCallStmt: After ProcessCallStmt
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(157,21)"} true;
    }
    else
    {
    }
}



procedure {:_induction n#0, k#0} CheckWellformed$$_module.__default.C__Correct(n#0: int where LitInt(0) <= n#0, k#0: int);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction n#0, k#0} CheckWellformed$$_module.__default.C__Correct(n#0: int, k#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##f#0: HandleType;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##n#1: int;
  var ##s#0: DatatypeType;

    // AddMethodImpl: C_Correct, CheckWellformed$$_module.__default.C__Correct
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(161,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(162,49): post-state"} true;
    assert 9 != $FunctionContextHeight;
    assume _module.__default.ones#canCall();
    assume _module.Stream.Cons_q(Lit(_module.__default.ones($LS($LZ))));
    ##n#0 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, TInt, $Heap);
    assume _module.__default.from#canCall(k#0);
    assume _module.Stream.Cons_q(_module.__default.from($LS($LZ), k#0));
    ##f#0 := _module.__default.plus#Handle();
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#0, Tclass._System.___hTotalFunc2(TInt, TInt, TInt), $Heap);
    ##a#0 := Lit(_module.__default.ones($LS($LZ)));
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, Tclass._module.Stream(TInt), $Heap);
    ##b#0 := _module.__default.from($LS($LZ), k#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.Combine#canCall(TInt, 
      _module.__default.plus#Handle(), 
      Lit(_module.__default.ones($LS($LZ))), 
      _module.__default.from($LS($LZ), k#0));
    assume _module.Stream.Cons_q(_module.__default.Combine(TInt, 
        $LS($LZ), 
        _module.__default.plus#Handle(), 
        Lit(_module.__default.ones($LS($LZ))), 
        _module.__default.from($LS($LZ), k#0)));
    ##n#1 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    ##s#0 := _module.__default.Combine(TInt, 
      $LS($LZ), 
      _module.__default.plus#Handle(), 
      Lit(_module.__default.ones($LS($LZ))), 
      _module.__default.from($LS($LZ), k#0));
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.nth#canCall(TInt, 
      n#0, 
      _module.__default.Combine(TInt, 
        $LS($LZ), 
        _module.__default.plus#Handle(), 
        Lit(_module.__default.ones($LS($LZ))), 
        _module.__default.from($LS($LZ), k#0)));
    assume $Unbox(_module.__default.nth(TInt, 
          $LS($LZ), 
          n#0, 
          _module.__default.Combine(TInt, 
            $LS($LZ), 
            _module.__default.plus#Handle(), 
            Lit(_module.__default.ones($LS($LZ))), 
            _module.__default.from($LS($LZ), k#0)))): int
       == k#0 + 1 + n#0;
}



procedure {:_induction n#0, k#0} Call$$_module.__default.C__Correct(n#0: int where LitInt(0) <= n#0, k#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ones#canCall()
     && _module.__default.from#canCall(k#0)
     && _module.__default.Combine#canCall(TInt, 
      _module.__default.plus#Handle(), 
      Lit(_module.__default.ones($LS($LZ))), 
      _module.__default.from($LS($LZ), k#0))
     && _module.__default.nth#canCall(TInt, 
      n#0, 
      _module.__default.Combine(TInt, 
        $LS($LZ), 
        _module.__default.plus#Handle(), 
        Lit(_module.__default.ones($LS($LZ))), 
        _module.__default.from($LS($LZ), k#0)));
  ensures $Unbox(_module.__default.nth(TInt, 
        $LS($LS($LZ)), 
        n#0, 
        _module.__default.Combine(TInt, 
          $LS($LS($LZ)), 
          _module.__default.plus#Handle(), 
          Lit(_module.__default.ones($LS($LS($LZ)))), 
          _module.__default.from($LS($LS($LZ)), k#0)))): int
     == k#0 + 1 + n#0;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, k#0} Impl$$_module.__default.C__Correct(n#0: int where LitInt(0) <= n#0, k#0: int) returns ($_reverifyPost: bool);
  free requires 33 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.ones#canCall()
     && _module.__default.from#canCall(k#0)
     && _module.__default.Combine#canCall(TInt, 
      _module.__default.plus#Handle(), 
      Lit(_module.__default.ones($LS($LZ))), 
      _module.__default.from($LS($LZ), k#0))
     && _module.__default.nth#canCall(TInt, 
      n#0, 
      _module.__default.Combine(TInt, 
        $LS($LZ), 
        _module.__default.plus#Handle(), 
        Lit(_module.__default.ones($LS($LZ))), 
        _module.__default.from($LS($LZ), k#0)));
  ensures $Unbox(_module.__default.nth(TInt, 
        $LS($LS($LZ)), 
        n#0, 
        _module.__default.Combine(TInt, 
          $LS($LS($LZ)), 
          _module.__default.plus#Handle(), 
          Lit(_module.__default.ones($LS($LS($LZ)))), 
          _module.__default.from($LS($LS($LZ)), k#0)))): int
     == k#0 + 1 + n#0;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, k#0} Impl$$_module.__default.C__Correct(n#0: int, k#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: C_Correct, Impl$$_module.__default.C__Correct
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(163,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: int, $ih#k0#0: int :: 
      LitInt(0) <= $ih#n0#0
           && Lit(true)
           && ((0 <= $ih#n0#0 && $ih#n0#0 < n#0)
             || ($ih#n0#0 == n#0 && 0 <= $ih#k0#0 && $ih#k0#0 < k#0))
         ==> $Unbox(_module.__default.nth(TInt, 
              $LS($LZ), 
              $ih#n0#0, 
              _module.__default.Combine(TInt, 
                $LS($LZ), 
                _module.__default.plus#Handle(), 
                Lit(_module.__default.ones($LS($LZ))), 
                _module.__default.from($LS($LZ), $ih#k0#0)))): int
           == $ih#k0#0 + 1 + $ih#n0#0);
    $_reverifyPost := false;
}



procedure CheckWellformed$$_module.__default.CombinePlus__Correct(a#0: DatatypeType
       where $Is(a#0, Tclass._module.Stream(TInt))
         && $IsAlloc(a#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(a#0), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.Stream(TInt))
         && $IsAlloc(b#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(b#0));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.CombinePlus__Correct(a#0: DatatypeType, b#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##f#0: HandleType;
  var ##a#0: DatatypeType;
  var ##b#0: DatatypeType;
  var ##a#1: DatatypeType;
  var ##b#1: DatatypeType;

    // AddMethodImpl: CombinePlus_Correct, CheckWellformed$$_module.__default.CombinePlus__Correct
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(166,15): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(167,30): post-state"} true;
    assert 9 != $FunctionContextHeight;
    ##f#0 := _module.__default.plus#Handle();
    // assume allocatedness for argument to function
    assume $IsAlloc(##f#0, Tclass._System.___hTotalFunc2(TInt, TInt, TInt), $Heap);
    ##a#0 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#0, Tclass._module.Stream(TInt), $Heap);
    ##b#0 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.Combine#canCall(TInt, _module.__default.plus#Handle(), a#0, b#0);
    assume _module.Stream.Cons_q(_module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), a#0, b#0));
    ##a#1 := a#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##a#1, Tclass._module.Stream(TInt), $Heap);
    ##b#1 := b#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##b#1, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.add#canCall(a#0, b#0);
    assume _module.Stream.Cons_q(_module.__default.add($LS($LZ), a#0, b#0));
    assume $Eq#_module.Stream(TInt, 
      TInt, 
      $LS($LS($LZ)), 
      _module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), a#0, b#0), 
      _module.__default.add($LS($LZ), a#0, b#0));
}



procedure Call$$_module.__default.CombinePlus__Correct(a#0: DatatypeType
       where $Is(a#0, Tclass._module.Stream(TInt))
         && $IsAlloc(a#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(a#0), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.Stream(TInt))
         && $IsAlloc(b#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(b#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures $IsA#_module.Stream(_module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), a#0, b#0))
     && $IsA#_module.Stream(_module.__default.add($LS($LZ), a#0, b#0))
     && 
    _module.__default.Combine#canCall(TInt, _module.__default.plus#Handle(), a#0, b#0)
     && _module.__default.add#canCall(a#0, b#0);
  ensures $Eq#_module.Stream(TInt, 
    TInt, 
    $LS($LS($LZ)), 
    _module.__default.Combine(TInt, $LS($LS($LZ)), _module.__default.plus#Handle(), a#0, b#0), 
    _module.__default.add($LS($LS($LZ)), a#0, b#0));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, a#1, b#1} CoCall$$_module.__default.CombinePlus__Correct_h(_k#0: Box, 
    a#1: DatatypeType
       where $Is(a#1, Tclass._module.Stream(TInt))
         && $IsAlloc(a#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(a#1), 
    b#1: DatatypeType
       where $Is(b#1, Tclass._module.Stream(TInt))
         && $IsAlloc(b#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(b#1));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Combine#canCall(TInt, _module.__default.plus#Handle(), a#1, b#1)
     && _module.__default.add#canCall(a#1, b#1);
  free ensures $PrefixEq#_module.Stream(TInt, 
    TInt, 
    _k#0, 
    $LS($LS($LZ)), 
    _module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), a#1, b#1), 
    _module.__default.add($LS($LZ), a#1, b#1));
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction _k#0, a#1, b#1} Impl$$_module.__default.CombinePlus__Correct_h(_k#0: Box, 
    a#1: DatatypeType
       where $Is(a#1, Tclass._module.Stream(TInt))
         && $IsAlloc(a#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(a#1), 
    b#1: DatatypeType
       where $Is(b#1, Tclass._module.Stream(TInt))
         && $IsAlloc(b#1, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(b#1))
   returns ($_reverifyPost: bool);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Combine#canCall(TInt, _module.__default.plus#Handle(), a#1, b#1)
     && _module.__default.add#canCall(a#1, b#1);
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), a#1, b#1), 
      _module.__default.add($LS($LZ), a#1, b#1))
     || (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.Combine(TInt, $LS($LS($LZ)), _module.__default.plus#Handle(), a#1, b#1))
       ==> _module.Stream.Cons_q(_module.__default.add($LS($LS($LZ)), a#1, b#1))
         && 
        $Unbox(_module.Stream.head(_module.__default.Combine(TInt, $LS($LS($LZ)), _module.__default.plus#Handle(), a#1, b#1))): int
           == $Unbox(_module.Stream.head(_module.__default.add($LS($LS($LZ)), a#1, b#1))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Combine(TInt, $LS($LS($LZ)), _module.__default.plus#Handle(), a#1, b#1)), 
          _module.Stream.tail(_module.__default.add($LS($LS($LZ)), a#1, b#1))));
  ensures $PrefixEq#_module.Stream(TInt, 
      TInt, 
      _k#0, 
      $LS($LS($LZ)), 
      _module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), a#1, b#1), 
      _module.__default.add($LS($LZ), a#1, b#1))
     || 
    (0 < ORD#Offset(_k#0)
       ==> 
      _module.Stream.Cons_q(_module.__default.Combine(TInt, $LS($LS($LZ)), _module.__default.plus#Handle(), a#1, b#1))
       ==> _module.Stream.Cons_q(_module.__default.add($LS($LS($LZ)), a#1, b#1))
         && 
        $Unbox(_module.Stream.head(_module.__default.Combine(TInt, $LS($LS($LZ)), _module.__default.plus#Handle(), a#1, b#1))): int
           == $Unbox(_module.Stream.head(_module.__default.add($LS($LS($LZ)), a#1, b#1))): int
         && $PrefixEq#_module.Stream(TInt, 
          TInt, 
          ORD#Minus(_k#0, ORD#FromNat(1)), 
          $LS($LS($LZ)), 
          _module.Stream.tail(_module.__default.Combine(TInt, $LS($LS($LZ)), _module.__default.plus#Handle(), a#1, b#1)), 
          _module.Stream.tail(_module.__default.add($LS($LS($LZ)), a#1, b#1))))
     || (_k#0 != ORD#FromNat(0) && ORD#IsLimit(_k#0)
       ==> $Eq#_module.Stream(TInt, 
        TInt, 
        $LS($LS($LZ)), 
        _module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), a#1, b#1), 
        _module.__default.add($LS($LZ), a#1, b#1)));
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction _k#0, a#1, b#1} Impl$$_module.__default.CombinePlus__Correct_h(_k#0: Box, a#1: DatatypeType, b#1: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var $initHeapForallStmt#1: Heap;

    // AddMethodImpl: CombinePlus_Correct#, Impl$$_module.__default.CombinePlus__Correct_h
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(166,15): initial state"} true;
    assume $IsA#_module.Stream(a#1);
    assume $IsA#_module.Stream(b#1);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#_k0#0: Box, $ih#a0#0: DatatypeType, $ih#b0#0: DatatypeType :: 
      $Is($ih#a0#0, Tclass._module.Stream(TInt))
           && $Is($ih#b0#0, Tclass._module.Stream(TInt))
           && Lit(true)
           && ORD#Less($ih#_k0#0, _k#0)
         ==> $PrefixEq#_module.Stream(TInt, 
          TInt, 
          $ih#_k0#0, 
          $LS($LS($LZ)), 
          _module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), $ih#a0#0, $ih#b0#0), 
          _module.__default.add($LS($LZ), $ih#a0#0, $ih#b0#0)));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(168,1)
    assume true;
    if (0 < ORD#Offset(_k#0))
    {
    }
    else
    {
        // ----- forall statement (call) ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(166,16)
        $initHeapForallStmt#1 := $Heap;
        havoc $Heap, $Tick;
        assume $initHeapForallStmt#1 == $Heap;
        assume (forall _k'#0: Box, a#2: DatatypeType, b#2: DatatypeType :: 
          $Is(a#2, Tclass._module.Stream(TInt))
               && $Is(b#2, Tclass._module.Stream(TInt))
               && ORD#Less(_k'#0, _k#0)
             ==> $PrefixEq#_module.Stream(TInt, 
              TInt, 
              _k'#0, 
              $LS($LS($LZ)), 
              _module.__default.Combine(TInt, $LS($LZ), _module.__default.plus#Handle(), a#2, b#2), 
              _module.__default.add($LS($LZ), a#2, b#2)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(166,15)"} true;
    }
}



procedure {:_induction n#0, a#0, b#0} CheckWellformed$$_module.__default.add__Correct(n#0: int where LitInt(0) <= n#0, 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.Stream(TInt))
         && $IsAlloc(a#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(a#0), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.Stream(TInt))
         && $IsAlloc(b#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(b#0));
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0, a#0, b#0} Call$$_module.__default.add__Correct(n#0: int where LitInt(0) <= n#0, 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.Stream(TInt))
         && $IsAlloc(a#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(a#0), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.Stream(TInt))
         && $IsAlloc(b#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(b#0));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.add#canCall(a#0, b#0)
     && _module.__default.nth#canCall(TInt, n#0, _module.__default.add($LS($LZ), a#0, b#0))
     && 
    _module.__default.nth#canCall(TInt, n#0, a#0)
     && _module.__default.nth#canCall(TInt, n#0, b#0);
  ensures $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, _module.__default.add($LS($LS($LZ)), a#0, b#0))): int
     == $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, a#0)): int
       + $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, b#0)): int;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, a#0, b#0} Impl$$_module.__default.add__Correct(n#0: int where LitInt(0) <= n#0, 
    a#0: DatatypeType
       where $Is(a#0, Tclass._module.Stream(TInt))
         && $IsAlloc(a#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(a#0), 
    b#0: DatatypeType
       where $Is(b#0, Tclass._module.Stream(TInt))
         && $IsAlloc(b#0, Tclass._module.Stream(TInt), $Heap)
         && $IsA#_module.Stream(b#0))
   returns ($_reverifyPost: bool);
  free requires 34 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.add#canCall(a#0, b#0)
     && _module.__default.nth#canCall(TInt, n#0, _module.__default.add($LS($LZ), a#0, b#0))
     && 
    _module.__default.nth#canCall(TInt, n#0, a#0)
     && _module.__default.nth#canCall(TInt, n#0, b#0);
  ensures $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, _module.__default.add($LS($LS($LZ)), a#0, b#0))): int
     == $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, a#0)): int
       + $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, b#0)): int;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, a#0, b#0} Impl$$_module.__default.add__Correct(n#0: int, a#0: DatatypeType, b#0: DatatypeType) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: add_Correct, Impl$$_module.__default.add__Correct
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(173,0): initial state"} true;
    assume $IsA#_module.Stream(a#0);
    assume $IsA#_module.Stream(b#0);
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: int, $ih#a0#0: DatatypeType, $ih#b0#0: DatatypeType :: 
      LitInt(0) <= $ih#n0#0
           && $Is($ih#a0#0, Tclass._module.Stream(TInt))
           && $Is($ih#b0#0, Tclass._module.Stream(TInt))
           && Lit(true)
           && 
          0 <= $ih#n0#0
           && $ih#n0#0 < n#0
         ==> $Unbox(_module.__default.nth(TInt, $LS($LZ), $ih#n0#0, _module.__default.add($LS($LZ), $ih#a0#0, $ih#b0#0))): int
           == $Unbox(_module.__default.nth(TInt, $LS($LZ), $ih#n0#0, $ih#a0#0)): int
             + $Unbox(_module.__default.nth(TInt, $LS($LZ), $ih#n0#0, $ih#b0#0)): int);
    $_reverifyPost := false;
}



// function declaration for _module._default.StraightFibonacci
function _module.__default.StraightFibonacci($ly: LayerType, n#0: int) : DatatypeType;

function _module.__default.StraightFibonacci#canCall(n#0: int) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.StraightFibonacci($LS($ly), n#0) } 
  _module.__default.StraightFibonacci($LS($ly), n#0)
     == _module.__default.StraightFibonacci($ly, n#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.StraightFibonacci(AsFuelBottom($ly), n#0) } 
  _module.__default.StraightFibonacci($ly, n#0)
     == _module.__default.StraightFibonacci($LZ, n#0));

// consequence axiom for _module.__default.StraightFibonacci
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.StraightFibonacci($ly, n#0) } 
    _module.__default.StraightFibonacci#canCall(n#0)
         || (35 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> $Is(_module.__default.StraightFibonacci($ly, n#0), Tclass._module.Stream(TInt)));

function _module.__default.StraightFibonacci#requires(LayerType, int) : bool;

// #requires axiom for _module.__default.StraightFibonacci
axiom (forall $ly: LayerType, n#0: int :: 
  { _module.__default.StraightFibonacci#requires($ly, n#0) } 
  LitInt(0) <= n#0
     ==> _module.__default.StraightFibonacci#requires($ly, n#0) == true);

// definition axiom for _module.__default.StraightFibonacci (revealed)
axiom 35 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, n#0: int :: 
    { _module.__default.StraightFibonacci($LS($ly), n#0) } 
    _module.__default.StraightFibonacci#canCall(n#0)
         || (35 != $FunctionContextHeight && LitInt(0) <= n#0)
       ==> _module.__default.nfib#canCall(n#0)
         && _module.__default.StraightFibonacci#canCall(n#0 + 1)
         && _module.__default.StraightFibonacci($LS($ly), n#0)
           == #_module.Stream.Cons($Box(_module.__default.nfib($LS($LZ), n#0)), 
            _module.__default.StraightFibonacci($ly, n#0 + 1)));

procedure CheckWellformed$$_module.__default.StraightFibonacci(n#0: int where LitInt(0) <= n#0);
  free requires 35 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.StraightFibonacci(n#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##n#1: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function StraightFibonacci
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(176,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        assume $Is(_module.__default.StraightFibonacci($LS($LZ), n#0), Tclass._module.Stream(TInt));
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
        assume _module.__default.nfib#canCall(n#0);
        assert $Is(n#0 + 1, Tclass._System.nat());
        ##n#1 := n#0 + 1;
        // assume allocatedness for argument to function
        assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume _module.__default.StraightFibonacci#canCall(n#0 + 1);
        assume _module.Stream.Cons_q(_module.__default.StraightFibonacci($LS($LZ), n#0 + 1));
        assume _module.__default.StraightFibonacci($LS($LZ), n#0)
           == #_module.Stream.Cons($Box(_module.__default.nfib($LS($LZ), n#0)), 
            _module.__default.StraightFibonacci($LS($LZ), n#0 + 1));
        assume _module.__default.nfib#canCall(n#0)
           && _module.__default.StraightFibonacci#canCall(n#0 + 1);
        // CheckWellformedWithResult: any expression
        assume $Is(_module.__default.StraightFibonacci($LS($LZ), n#0), Tclass._module.Stream(TInt));
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



procedure {:_induction n#0, k#0} CheckWellformed$$_module.__default.StraightFibonacci__Correct(n#0: int where LitInt(0) <= n#0, k#0: int where LitInt(0) <= k#0);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation {:_induction n#0, k#0} CheckWellformed$$_module.__default.StraightFibonacci__Correct(n#0: int, k#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##n#0: int;
  var ##n#1: int;
  var ##s#0: DatatypeType;
  var ##n#2: int;

    // AddMethodImpl: StraightFibonacci_Correct, CheckWellformed$$_module.__default.StraightFibonacci__Correct
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(181,6): initial state"} true;
    havoc $Heap;
    assume old($Heap) == $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(182,39): post-state"} true;
    ##n#0 := k#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#0, Tclass._System.nat(), $Heap);
    assume _module.__default.StraightFibonacci#canCall(k#0);
    assume _module.Stream.Cons_q(_module.__default.StraightFibonacci($LS($LZ), k#0));
    ##n#1 := n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#1, Tclass._System.nat(), $Heap);
    ##s#0 := _module.__default.StraightFibonacci($LS($LZ), k#0);
    // assume allocatedness for argument to function
    assume $IsAlloc(##s#0, Tclass._module.Stream(TInt), $Heap);
    assume _module.__default.nth#canCall(TInt, n#0, _module.__default.StraightFibonacci($LS($LZ), k#0));
    assert $Is(k#0 + n#0, Tclass._System.nat());
    ##n#2 := k#0 + n#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##n#2, Tclass._System.nat(), $Heap);
    assume _module.__default.nfib#canCall(k#0 + n#0);
    assume $Unbox(_module.__default.nth(TInt, $LS($LZ), n#0, _module.__default.StraightFibonacci($LS($LZ), k#0))): int
       == _module.__default.nfib($LS($LZ), k#0 + n#0);
}



procedure {:_induction n#0, k#0} Call$$_module.__default.StraightFibonacci__Correct(n#0: int where LitInt(0) <= n#0, k#0: int where LitInt(0) <= k#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.StraightFibonacci#canCall(k#0)
     && _module.__default.nth#canCall(TInt, n#0, _module.__default.StraightFibonacci($LS($LZ), k#0))
     && _module.__default.nfib#canCall(k#0 + n#0);
  ensures $Unbox(_module.__default.nth(TInt, 
        $LS($LS($LZ)), 
        n#0, 
        _module.__default.StraightFibonacci($LS($LS($LZ)), k#0))): int
     == _module.__default.nfib($LS($LS($LZ)), k#0 + n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0, k#0} Impl$$_module.__default.StraightFibonacci__Correct(n#0: int where LitInt(0) <= n#0, k#0: int where LitInt(0) <= k#0)
   returns ($_reverifyPost: bool);
  free requires 36 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.StraightFibonacci#canCall(k#0)
     && _module.__default.nth#canCall(TInt, n#0, _module.__default.StraightFibonacci($LS($LZ), k#0))
     && _module.__default.nfib#canCall(k#0 + n#0);
  ensures $Unbox(_module.__default.nth(TInt, 
        $LS($LS($LZ)), 
        n#0, 
        _module.__default.StraightFibonacci($LS($LS($LZ)), k#0))): int
     == _module.__default.nfib($LS($LS($LZ)), k#0 + n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0, k#0} Impl$$_module.__default.StraightFibonacci__Correct(n#0: int, k#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;

    // AddMethodImpl: StraightFibonacci_Correct, Impl$$_module.__default.StraightFibonacci__Correct
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(183,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: int, $ih#k0#0: int :: 
      LitInt(0) <= $ih#n0#0
           && LitInt(0) <= $ih#k0#0
           && Lit(true)
           && ((0 <= $ih#n0#0 && $ih#n0#0 < n#0)
             || ($ih#n0#0 == n#0 && 0 <= $ih#k0#0 && $ih#k0#0 < k#0))
         ==> $Unbox(_module.__default.nth(TInt, 
              $LS($LZ), 
              $ih#n0#0, 
              _module.__default.StraightFibonacci($LS($LZ), $ih#k0#0))): int
           == _module.__default.nfib($LS($LZ), $ih#k0#0 + $ih#n0#0));
    $_reverifyPost := false;
}



procedure {:_induction n#0} CheckWellformed$$_module.__default.Fib__Correct(n#0: int where LitInt(0) <= n#0);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure {:_induction n#0} Call$$_module.__default.Fib__Correct(n#0: int where LitInt(0) <= n#0);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Fib#canCall()
     && _module.__default.nth#canCall(TInt, n#0, Lit(_module.__default.Fib($LS($LZ))))
     && _module.__default.nfib#canCall(n#0);
  ensures $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, Lit(_module.__default.Fib($LS($LS($LZ)))))): int
     == _module.__default.nfib($LS($LS($LZ)), n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



procedure {:_induction n#0} Impl$$_module.__default.Fib__Correct(n#0: int where LitInt(0) <= n#0) returns ($_reverifyPost: bool);
  free requires 37 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures _module.__default.Fib#canCall()
     && _module.__default.nth#canCall(TInt, n#0, Lit(_module.__default.Fib($LS($LZ))))
     && _module.__default.nfib#canCall(n#0);
  ensures $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, Lit(_module.__default.Fib($LS($LS($LZ)))))): int
     == _module.__default.nfib($LS($LS($LZ)), n#0);
  // frame condition
  free ensures old($Heap) == $Heap;



implementation {:_induction n#0} Impl$$_module.__default.Fib__Correct(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $initHeapForallStmt#0: Heap;
  var F#0: DatatypeType
     where $Is(F#0, Tclass._module.Stream(TInt))
       && $IsAlloc(F#0, Tclass._module.Stream(TInt), $Heap);
  var ##n#1_0_0: int;
  var ##n#1_0_1: int;
  var ##n#1_0_2: int;
  var ##n#1_1_0: int;
  var ##s#1_1_0: DatatypeType;
  var ##n#1_1_1: int;
  var ##s#1_1_1: DatatypeType;
  var n##1_1_0: int;
  var n##1_1_1: int;
  var ##n#1_1_2: int;
  var ##n#1_1_3: int;
  var ##n#1_2_0: int;
  var ##s#1_2_0: DatatypeType;
  var ##n#1_2_1: int;
  var ##s#1_2_1: DatatypeType;
  var ##n#1_2_2: int;
  var ##s#1_2_2: DatatypeType;
  var ##n#1_2_3: int;
  var ##s#1_2_3: DatatypeType;
  var ##a#1_3_0: DatatypeType;
  var ##b#1_3_0: DatatypeType;
  var ##n#1_3_0: int;
  var ##s#1_3_0: DatatypeType;
  var n##1_3_0: int;
  var a##1_3_0: DatatypeType;
  var b##1_3_0: DatatypeType;
  var ##n#1_3_1: int;
  var ##s#1_3_1: DatatypeType;
  var ##n#1_3_2: int;
  var ##s#1_3_2: DatatypeType;
  var ##n#1_4_0: int;
  var ##s#1_4_0: DatatypeType;
  var ##a#1_4_0: DatatypeType;
  var ##b#1_4_0: DatatypeType;
  var ##n#1_4_1: int;
  var ##s#1_4_1: DatatypeType;
  var ##n#1_5_0: int;
  var ##s#1_5_0: DatatypeType;
  var ##n#1_5_1: int;
  var ##s#1_5_1: DatatypeType;
  var ##n#1_0: int;
  var ##s#1_0: DatatypeType;

    // AddMethodImpl: Fib_Correct, Impl$$_module.__default.Fib__Correct
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(188,0): initial state"} true;
    $initHeapForallStmt#0 := $Heap;
    havoc $Heap, $Tick;
    assume $initHeapForallStmt#0 == $Heap;
    assume (forall $ih#n0#0: int :: 
      LitInt(0) <= $ih#n0#0 && Lit(true) && 0 <= $ih#n0#0 && $ih#n0#0 < n#0
         ==> $Unbox(_module.__default.nth(TInt, $LS($LZ), $ih#n0#0, Lit(_module.__default.Fib($LS($LZ))))): int
           == _module.__default.nfib($LS($LZ), $ih#n0#0));
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(189,3)
    assume true;
    if (n#0 < 2)
    {
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(191,12)
        assume true;
        assume _module.__default.Fib#canCall();
        assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
        assume _module.__default.Fib#canCall();
        F#0 := Lit(_module.__default.Fib($LS($LZ)));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(191,19)"} true;
        // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
        // Assume Fuel Constant
        if (*)
        {
            // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            ##n#1_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0, Tclass._System.nat(), $Heap);
            ##s#1_0 := F#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0, F#0);
            assume _module.__default.nth#canCall(TInt, n#0, F#0);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            ##n#1_5_0 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_5_0, Tclass._System.nat(), $Heap);
            ##s#1_5_0 := F#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_5_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0, F#0);
            assume _module.__default.nth#canCall(TInt, n#0, F#0);
            // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume _module.Stream.Cons_q(F#0);
            assume _module.Stream.Cons_q(_module.Stream.tail(F#0));
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_5_1 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_5_1, Tclass._System.nat(), $Heap);
            ##s#1_5_1 := _module.Stream.tail(_module.Stream.tail(F#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_5_1, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 2, _module.Stream.tail(_module.Stream.tail(F#0)));
            assume _module.Stream.Cons_q(F#0)
               && _module.Stream.Cons_q(_module.Stream.tail(F#0))
               && _module.__default.nth#canCall(TInt, n#0 - 2, _module.Stream.tail(_module.Stream.tail(F#0)));
            // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assert {:subsumption 0} $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0, F#0)): int
               == $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0 - 2, _module.Stream.tail(_module.Stream.tail(F#0)))): int;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume _module.Stream.Cons_q(F#0);
            assume _module.Stream.Cons_q(_module.Stream.tail(F#0));
            assume $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_4_0 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_4_0, Tclass._System.nat(), $Heap);
            ##s#1_4_0 := _module.Stream.tail(_module.Stream.tail(F#0));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_4_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 2, _module.Stream.tail(_module.Stream.tail(F#0)));
            assume _module.Stream.Cons_q(F#0)
               && _module.Stream.Cons_q(_module.Stream.tail(F#0))
               && _module.__default.nth#canCall(TInt, n#0 - 2, _module.Stream.tail(_module.Stream.tail(F#0)));
            // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            ##a#1_4_0 := Lit(_module.__default.Fib($LS($LZ)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1_4_0, Tclass._module.Stream(TInt), $Heap);
            ##b#1_4_0 := Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1_4_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.add#canCall(Lit(_module.__default.Fib($LS($LZ))), 
              Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))));
            assume _module.Stream.Cons_q(Lit(_module.__default.add($LS($LZ), 
                  Lit(_module.__default.Fib($LS($LZ))), 
                  Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))));
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_4_1 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_4_1, Tclass._System.nat(), $Heap);
            ##s#1_4_1 := Lit(_module.__default.add($LS($LZ), 
                Lit(_module.__default.Fib($LS($LZ))), 
                Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_4_1, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, 
              n#0 - 2, 
              Lit(_module.__default.add($LS($LZ), 
                  Lit(_module.__default.Fib($LS($LZ))), 
                  Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))));
            assume _module.__default.Fib#canCall()
               && 
              _module.__default.Fib#canCall()
               && _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))))
               && _module.__default.add#canCall(Lit(_module.__default.Fib($LS($LZ))), 
                Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))
               && _module.__default.nth#canCall(TInt, 
                n#0 - 2, 
                Lit(_module.__default.add($LS($LZ), 
                    Lit(_module.__default.Fib($LS($LZ))), 
                    Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))));
            // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assert {:subsumption 0} $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0 - 2, _module.Stream.tail(_module.Stream.tail(F#0)))): int
               == $Unbox(_module.__default.nth(TInt, 
                  $LS($LS($LZ)), 
                  n#0 - 2, 
                  Lit(_module.__default.add($LS($LS($LZ)), 
                      Lit(_module.__default.Fib($LS($LS($LZ)))), 
                      Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LS($LZ)))))))))): int;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            ##a#1_3_0 := Lit(_module.__default.Fib($LS($LZ)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##a#1_3_0, Tclass._module.Stream(TInt), $Heap);
            ##b#1_3_0 := Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##b#1_3_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.add#canCall(Lit(_module.__default.Fib($LS($LZ))), 
              Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))));
            assume _module.Stream.Cons_q(Lit(_module.__default.add($LS($LZ), 
                  Lit(_module.__default.Fib($LS($LZ))), 
                  Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))));
            assume $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_3_0 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_3_0, Tclass._System.nat(), $Heap);
            ##s#1_3_0 := Lit(_module.__default.add($LS($LZ), 
                Lit(_module.__default.Fib($LS($LZ))), 
                Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_3_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, 
              n#0 - 2, 
              Lit(_module.__default.add($LS($LZ), 
                  Lit(_module.__default.Fib($LS($LZ))), 
                  Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))));
            assume _module.__default.Fib#canCall()
               && 
              _module.__default.Fib#canCall()
               && _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))))
               && _module.__default.add#canCall(Lit(_module.__default.Fib($LS($LZ))), 
                Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))
               && _module.__default.nth#canCall(TInt, 
                n#0 - 2, 
                Lit(_module.__default.add($LS($LZ), 
                    Lit(_module.__default.Fib($LS($LZ))), 
                    Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))))));
            // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(198,22)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0 - 2, Tclass._System.nat());
            n##1_3_0 := n#0 - 2;
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall();
            // ProcessCallStmt: CheckSubrange
            a##1_3_0 := Lit(_module.__default.Fib($LS($LZ)));
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall()
               && _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            // ProcessCallStmt: CheckSubrange
            b##1_3_0 := Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))));
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.add__Correct(n##1_3_0, a##1_3_0, b##1_3_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(198,45)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_3_1 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_3_1, Tclass._System.nat(), $Heap);
            ##s#1_3_1 := Lit(_module.__default.Fib($LS($LZ)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_3_1, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_3_2 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_3_2, Tclass._System.nat(), $Heap);
            ##s#1_3_2 := Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_3_2, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))));
            assume _module.__default.Fib#canCall()
               && _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.__default.Fib($LS($LZ))))
               && 
              _module.__default.Fib#canCall()
               && _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))))
               && _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))));
            // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assert {:subsumption 0} $Unbox(_module.__default.nth(TInt, 
                  $LS($LS($LZ)), 
                  n#0 - 2, 
                  Lit(_module.__default.add($LS($LS($LZ)), 
                      Lit(_module.__default.Fib($LS($LS($LZ)))), 
                      Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LS($LZ)))))))))): int
               == $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0 - 2, Lit(_module.__default.Fib($LS($LS($LZ)))))): int
                 + $Unbox(_module.__default.nth(TInt, 
                    $LS($LS($LZ)), 
                    n#0 - 2, 
                    Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LS($LZ)))))))): int;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_2_0 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_2_0, Tclass._System.nat(), $Heap);
            ##s#1_2_0 := Lit(_module.__default.Fib($LS($LZ)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_2_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_2_1 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_2_1, Tclass._System.nat(), $Heap);
            ##s#1_2_1 := Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ)))));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_2_1, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))));
            assume _module.__default.Fib#canCall()
               && _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.__default.Fib($LS($LZ))))
               && 
              _module.__default.Fib#canCall()
               && _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))))
               && _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LZ))))));
            // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_2_2 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_2_2, Tclass._System.nat(), $Heap);
            ##s#1_2_2 := Lit(_module.__default.Fib($LS($LZ)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_2_2, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_2_3 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_2_3, Tclass._System.nat(), $Heap);
            ##s#1_2_3 := Lit(_module.__default.Fib($LS($LZ)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_2_3, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 1, Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall()
               && _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.__default.Fib($LS($LZ))))
               && 
              _module.__default.Fib#canCall()
               && _module.__default.nth#canCall(TInt, n#0 - 1, Lit(_module.__default.Fib($LS($LZ))));
            // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assert {:subsumption 0} $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0 - 2, Lit(_module.__default.Fib($LS($LS($LZ)))))): int
                 + $Unbox(_module.__default.nth(TInt, 
                    $LS($LS($LZ)), 
                    n#0 - 2, 
                    Lit(_module.Stream.tail(Lit(_module.__default.Fib($LS($LS($LZ)))))))): int
               == $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0 - 2, Lit(_module.__default.Fib($LS($LS($LZ)))))): int
                 + $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0 - 1, Lit(_module.__default.Fib($LS($LS($LZ)))))): int;
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_1_0 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_0, Tclass._System.nat(), $Heap);
            ##s#1_1_0 := Lit(_module.__default.Fib($LS($LZ)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_1_0, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall();
            assume _module.Stream.Cons_q(Lit(_module.__default.Fib($LS($LZ))));
            assume $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_1_1 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_1, Tclass._System.nat(), $Heap);
            ##s#1_1_1 := Lit(_module.__default.Fib($LS($LZ)));
            // assume allocatedness for argument to function
            assume $IsAlloc(##s#1_1_1, Tclass._module.Stream(TInt), $Heap);
            assume _module.__default.nth#canCall(TInt, n#0 - 1, Lit(_module.__default.Fib($LS($LZ))));
            assume _module.__default.Fib#canCall()
               && _module.__default.nth#canCall(TInt, n#0 - 2, Lit(_module.__default.Fib($LS($LZ))))
               && 
              _module.__default.Fib#canCall()
               && _module.__default.nth#canCall(TInt, n#0 - 1, Lit(_module.__default.Fib($LS($LZ))));
            // ----- Hint4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(202,22)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0 - 2, Tclass._System.nat());
            n##1_1_0 := n#0 - 2;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || n##1_1_0 == n#0;
            assert n##1_1_0 < n#0;
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Fib__Correct(n##1_1_0);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(202,26)"} true;
            // ----- call statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(202,40)
            // TrCallStmt: Before ProcessCallStmt
            assume true;
            // ProcessCallStmt: CheckSubrange
            assert $Is(n#0 - 1, Tclass._System.nat());
            n##1_1_1 := n#0 - 1;
            assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assert 0 <= n#0 || n##1_1_1 == n#0;
            assert n##1_1_1 < n#0;
            // ProcessCallStmt: Make the call
            call Call$$_module.__default.Fib__Correct(n##1_1_1);
            // TrCallStmt: After ProcessCallStmt
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(202,44)"} true;
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assert $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_1_2 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_2, Tclass._System.nat(), $Heap);
            assume _module.__default.nfib#canCall(n#0 - 2);
            assert $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_1_3 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_1_3, Tclass._System.nat(), $Heap);
            assume _module.__default.nfib#canCall(n#0 - 1);
            assume _module.__default.nfib#canCall(n#0 - 2)
               && _module.__default.nfib#canCall(n#0 - 1);
            // ----- assert line4 == line5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assert {:subsumption 0} $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0 - 2, Lit(_module.__default.Fib($LS($LS($LZ)))))): int
                 + $Unbox(_module.__default.nth(TInt, $LS($LS($LZ)), n#0 - 1, Lit(_module.__default.Fib($LS($LS($LZ)))))): int
               == _module.__default.nfib($LS($LS($LZ)), n#0 - 2)
                 + _module.__default.nfib($LS($LS($LZ)), n#0 - 1);
            assume false;
        }
        else if (*)
        {
            // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assume $Is(n#0 - 2, Tclass._System.nat());
            ##n#1_0_0 := n#0 - 2;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0_0, Tclass._System.nat(), $Heap);
            assume _module.__default.nfib#canCall(n#0 - 2);
            assume $Is(n#0 - 1, Tclass._System.nat());
            ##n#1_0_1 := n#0 - 1;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0_1, Tclass._System.nat(), $Heap);
            assume _module.__default.nfib#canCall(n#0 - 1);
            assume _module.__default.nfib#canCall(n#0 - 2)
               && _module.__default.nfib#canCall(n#0 - 1);
            // ----- Hint5 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            ##n#1_0_2 := n#0;
            // assume allocatedness for argument to function
            assume $IsAlloc(##n#1_0_2, Tclass._System.nat(), $Heap);
            assume _module.__default.nfib#canCall(n#0);
            assume _module.__default.nfib#canCall(n#0);
            // ----- assert line5 == line6 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny3/Abstemious.dfy(192,5)
            assert {:subsumption 0} _module.__default.nfib($LS($LS($LZ)), n#0 - 2)
                 + _module.__default.nfib($LS($LS($LZ)), n#0 - 1)
               == _module.__default.nfib($LS($LS($LZ)), n#0);
            assume false;
        }

        assume $Unbox(_module.__default.nth(TInt, $LS($LZ), n#0, F#0)): int
           == _module.__default.nfib($LS($LZ), n#0);
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

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_#Func3: TyTagFamily;

const unique tytagFamily$_#PartialFunc3: TyTagFamily;

const unique tytagFamily$_#TotalFunc3: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$List: TyTagFamily;

const unique tytagFamily$Stream: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
