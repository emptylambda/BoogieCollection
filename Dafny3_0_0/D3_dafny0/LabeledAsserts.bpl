// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy -print:./LabeledAsserts.bpl

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

const unique class._module.C?: ClassName;

function Tclass._module.C?() : Ty;

const unique Tagclass._module.C?: TyTag;

// Tclass._module.C? Tag
axiom Tag(Tclass._module.C?()) == Tagclass._module.C?
   && TagFamily(Tclass._module.C?()) == tytagFamily$C;

// Box/unbox axiom for Tclass._module.C?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.C?()) } 
  $IsBox(bx, Tclass._module.C?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.C?()));

// C: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.C?()) } 
  $Is($o, Tclass._module.C?()) <==> $o == null || dtype($o) == Tclass._module.C?());

// C: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.C?(), $h) } 
  $IsAlloc($o, Tclass._module.C?(), $h) <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.C.g) == 0
   && FieldOfDecl(class._module.C?, field$g) == _module.C.g
   && !$IsGhostField(_module.C.g);

const _module.C.g: Field int;

// C.g: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.g) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.C?()
     ==> $Is(read($h, $o, _module.C.g), TInt));

// C.g: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.g) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.C.g), TInt, $h));

axiom FDim(_module.C.h) == 0
   && FieldOfDecl(class._module.C?, field$h) == _module.C.h
   && !$IsGhostField(_module.C.h);

const _module.C.h: Field int;

// C.h: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.h) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.C?()
     ==> $Is(read($h, $o, _module.C.h), TInt));

// C.h: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.C.h) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.C?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.C.h), TInt, $h));

function Tclass._module.C() : Ty;

const unique Tagclass._module.C: TyTag;

// Tclass._module.C Tag
axiom Tag(Tclass._module.C()) == Tagclass._module.C
   && TagFamily(Tclass._module.C()) == tytagFamily$C;

// Box/unbox axiom for Tclass._module.C
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.C()) } 
  $IsBox(bx, Tclass._module.C())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.C()));

// _module.C: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.C()) } 
  $Is(c#0, Tclass._module.C()) <==> $Is(c#0, Tclass._module.C?()) && c#0 != null);

// _module.C: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.C(), $h) } 
  $IsAlloc(c#0, Tclass._module.C(), $h)
     <==> $IsAlloc(c#0, Tclass._module.C?(), $h));

const unique class._module.Iter0?: ClassName;

function Tclass._module.Iter0?() : Ty;

const unique Tagclass._module.Iter0?: TyTag;

// Tclass._module.Iter0? Tag
axiom Tag(Tclass._module.Iter0?()) == Tagclass._module.Iter0?
   && TagFamily(Tclass._module.Iter0?()) == tytagFamily$Iter0;

// Box/unbox axiom for Tclass._module.Iter0?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Iter0?()) } 
  $IsBox(bx, Tclass._module.Iter0?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Iter0?()));

// Iter0: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Iter0?()) } 
  $Is($o, Tclass._module.Iter0?())
     <==> $o == null || dtype($o) == Tclass._module.Iter0?());

// Iter0: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Iter0?(), $h) } 
  $IsAlloc($o, Tclass._module.Iter0?(), $h) <==> $o == null || read($h, $o, alloc));

function _module.Iter0.x(ref) : int;

// Iter0.x: Type axiom
axiom (forall $o: ref :: 
  { _module.Iter0.x($o) } 
  $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(_module.Iter0.x($o), TInt));

// Iter0.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Iter0.x($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter0.x($o), TInt, $h));

function _module.Iter0.y(ref) : int;

// Iter0.y: Type axiom
axiom (forall $o: ref :: 
  { _module.Iter0.y($o) } 
  $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(_module.Iter0.y($o), TInt));

// Iter0.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Iter0.y($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter0.y($o), TInt, $h));

function _module.Iter0.z(ref) : int;

// Iter0.z: Type axiom
axiom (forall $o: ref :: 
  { _module.Iter0.z($o) } 
  $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(_module.Iter0.z($o), TInt));

// Iter0.z: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Iter0.z($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter0.z($o), TInt, $h));

axiom FDim(_module.Iter0.u) == 0
   && FieldOfDecl(class._module.Iter0?, field$u) == _module.Iter0.u
   && !$IsGhostField(_module.Iter0.u);

const _module.Iter0.u: Field int;

// Iter0.u: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter0.u) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(read($h, $o, _module.Iter0.u), TInt));

// Iter0.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter0.u) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Iter0.u), TInt, $h));

axiom FDim(_module.Iter0.us) == 0
   && FieldOfDecl(class._module.Iter0?, field$us) == _module.Iter0.us
   && $IsGhostField(_module.Iter0.us);

const _module.Iter0.us: Field (Seq Box);

// Iter0.us: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter0.us) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(read($h, $o, _module.Iter0.us), TSeq(TInt)));

// Iter0.us: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter0.us) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Iter0.us), TSeq(TInt), $h));

function _module.Iter0.__reads(ref) : Set Box;

// Iter0._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.Iter0.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(_module.Iter0.__reads($o), TSet(Tclass._System.object?())));

// Iter0._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Iter0.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter0.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.Iter0.__modifies(ref) : Set Box;

// Iter0._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.Iter0.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(_module.Iter0.__modifies($o), TSet(Tclass._System.object?())));

// Iter0._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Iter0.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter0.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.Iter0.__new) == 0
   && FieldOfDecl(class._module.Iter0?, field$_new) == _module.Iter0.__new
   && $IsGhostField(_module.Iter0.__new);

const _module.Iter0.__new: Field (Set Box);

// Iter0._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter0.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(read($h, $o, _module.Iter0.__new), TSet(Tclass._System.object?())));

// Iter0._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Iter0.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Iter0.__new), TSet(Tclass._System.object?()), $h));

function _module.Iter0.__decreases0(ref) : int;

// Iter0._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.Iter0.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(_module.Iter0.__decreases0($o), TInt));

// Iter0._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Iter0.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter0.__decreases0($o), TInt, $h));

function _module.Iter0.__decreases1(ref) : int;

// Iter0._decreases1: Type axiom
axiom (forall $o: ref :: 
  { _module.Iter0.__decreases1($o) } 
  $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(_module.Iter0.__decreases1($o), TInt));

// Iter0._decreases1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Iter0.__decreases1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter0.__decreases1($o), TInt, $h));

function _module.Iter0.__decreases2(ref) : int;

// Iter0._decreases2: Type axiom
axiom (forall $o: ref :: 
  { _module.Iter0.__decreases2($o) } 
  $o != null && dtype($o) == Tclass._module.Iter0?()
     ==> $Is(_module.Iter0.__decreases2($o), TInt));

// Iter0._decreases2: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.Iter0.__decreases2($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Iter0?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.Iter0.__decreases2($o), TInt, $h));

function Tclass._module.Iter0() : Ty;

const unique Tagclass._module.Iter0: TyTag;

// Tclass._module.Iter0 Tag
axiom Tag(Tclass._module.Iter0()) == Tagclass._module.Iter0
   && TagFamily(Tclass._module.Iter0()) == tytagFamily$Iter0;

// Box/unbox axiom for Tclass._module.Iter0
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Iter0()) } 
  $IsBox(bx, Tclass._module.Iter0())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Iter0()));

procedure CheckWellformed$$_module.Iter0.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter0())
         && $IsAlloc(this, Tclass._module.Iter0(), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int);
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Iter0.__ctor(x#0: int, y#0: int, z#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter0())
         && $IsAlloc(this, Tclass._module.Iter0(), $Heap));
  // user-defined preconditions
  requires LitInt(0) <= x#0;
  requires LitInt(0) <= y#0;
  requires LitInt(0) <= z#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.Iter0.x(this) == x#0;
  free ensures true;
  ensures _module.Iter0.y(this) == y#0;
  free ensures true;
  ensures _module.Iter0.z(this) == z#0;
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Iter0.us), Seq#Empty(): Seq Box);
  free ensures _module.Iter0.Valid#canCall($Heap, this);
  ensures _module.Iter0.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.Iter0.__reads(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(_module.Iter0.__modifies(this), Set#Empty(): Set Box);
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.Iter0.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.Iter0.__decreases0(this) == x#0;
  free ensures true;
  ensures _module.Iter0.__decreases1(this) == y#0;
  free ensures true;
  ensures _module.Iter0.__decreases2(this) == z#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.Iter0.Valid
function _module.Iter0.Valid($heap: Heap, this: ref) : bool;

function _module.Iter0.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.Iter0.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.Iter0.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.Iter0())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.Iter0.__reads(this)[$Box($o)]
             || read($h0, this, _module.Iter0.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.Iter0.Valid($h0, this) == _module.Iter0.Valid($h1, this));

// consequence axiom for _module.Iter0.Valid
axiom 8 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.Iter0.Valid($Heap, this) } 
    _module.Iter0.Valid#canCall($Heap, this)
         || (8 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.Iter0())
           && $IsAlloc(this, Tclass._module.Iter0(), $Heap))
       ==> true);

function _module.Iter0.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.Iter0.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.Iter0.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.Iter0())
       && $IsAlloc(this, Tclass._module.Iter0(), $Heap)
     ==> _module.Iter0.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.Iter0.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter0())
         && $IsAlloc(this, Tclass._module.Iter0(), $Heap));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.Iter0.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(19,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.Iter0.__reads(this)[$Box($o)]
           || read($Heap, this, _module.Iter0.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.Iter0.__new];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



procedure Call$$_module.Iter0.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter0())
         && $IsAlloc(this, Tclass._module.Iter0(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.Iter0.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.Iter0.__new)[$Box($o)]
         && !read(old($Heap), this, _module.Iter0.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.Iter0.__new)[$Box(null)];
  free ensures more#0 ==> _module.Iter0.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.Iter0.Valid($Heap, this);
  free ensures true;
  ensures Seq#Equal(read($Heap, this, _module.Iter0.us), 
    (if more#0
       then Seq#Append(read(old($Heap), this, _module.Iter0.us), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.Iter0.u))))
       else read(old($Heap), this, _module.Iter0.us)));
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.Iter0.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.Iter0.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.Iter0: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Iter0()) } 
  $Is(c#0, Tclass._module.Iter0())
     <==> $Is(c#0, Tclass._module.Iter0?()) && c#0 != null);

// _module.Iter0: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Iter0(), $h) } 
  $IsAlloc(c#0, Tclass._module.Iter0(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Iter0?(), $h));

procedure CheckWellformed$$_module.Iter0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter0())
         && $IsAlloc(this, Tclass._module.Iter0(), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int);
  free requires 18 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Impl$$_module.Iter0(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Iter0())
         && $IsAlloc(this, Tclass._module.Iter0(), $Heap), 
    x#0: int, 
    y#0: int, 
    z#0: int);
  free requires 18 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= x#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Iter0(this: ref, x#0: int, y#0: int, z#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int
     where _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter0.us));
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var $rhs#0: int;
  var $Heap_at_0: Heap;
  var $Heap_at_1: Heap;
  var $rhs#1: int;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(19,9): initial state"} true;
    assume LitInt(0) <= x#0;
    assume _module.Iter0.x(this) == x#0;
    assume _module.Iter0.y(this) == y#0;
    assume _module.Iter0.z(this) == z#0;
    assume Seq#Equal(read($Heap, this, _module.Iter0.us), Seq#Empty(): Seq Box);
    assume _module.Iter0.Valid($Heap, this);
    assume Set#Equal(_module.Iter0.__reads(this), Set#Empty(): Set Box);
    assume Set#Equal(_module.Iter0.__modifies(this), Set#Empty(): Set Box);
    assume Set#Equal(read($Heap, this, _module.Iter0.__new), Set#Empty(): Set Box);
    assume _module.Iter0.__decreases0(this) == x#0;
    assume _module.Iter0.__decreases1(this) == y#0;
    assume _module.Iter0.__decreases2(this) == z#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.Iter0.__reads(this), read($Heap, this, _module.Iter0.__new));
    $_OldIterHeap := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(24,3)
    assume true;
    assert LitInt(0) <= _module.Iter0.x(this);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(25,3)
    assume true;
    assert LitInt(0) <= _module.Iter0.y(this);
    // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(26,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(26,3)
    assume true;
    assert $_Frame[this, _module.Iter0.u];
    assume true;
    $rhs#0 := LitInt(20);
    $Heap := update($Heap, this, _module.Iter0.u, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(26,10)"} true;
    $Heap := update($Heap, 
      this, 
      _module.Iter0.us, 
      Seq#Append(read($Heap, this, _module.Iter0.us), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.Iter0.u)))));
    _yieldCount#0 := _yieldCount#0 + 1;
    assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter0.us));
    assume $IsGoodHeap($Heap);
    call $YieldHavoc(this, _module.Iter0.__reads(this), read($Heap, this, _module.Iter0.__new));
    $_OldIterHeap := $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(26,10)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(27,3)
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(27,3)
        assert _module.Iter0.x(this) + _module.Iter0.y(this) == LitInt(80);
        assume false;
    }

    $Heap_at_0 := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(28,3)
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(28,3)
        assert _module.Iter0.x(this) + _module.Iter0.y(this) == LitInt(80);
        assume false;
    }

    $Heap_at_1 := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(29,3)
    assume true;
    assert _module.Iter0.x(this) + _module.Iter0.y(this) == LitInt(80);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(30,3)
    assume true;
    assert _module.Iter0.x(this) + _module.Iter0.y(this) == LitInt(80);
    // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(31,3)
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(31,3)
    assume true;
    assert $_Frame[this, _module.Iter0.u];
    assume true;
    $rhs#1 := LitInt(30);
    $Heap := update($Heap, this, _module.Iter0.u, $rhs#1);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(31,10)"} true;
    $Heap := update($Heap, 
      this, 
      _module.Iter0.us, 
      Seq#Append(read($Heap, this, _module.Iter0.us), 
        Seq#Build(Seq#Empty(): Seq Box, $Box(read($Heap, this, _module.Iter0.u)))));
    _yieldCount#0 := _yieldCount#0 + 1;
    assume _yieldCount#0 == Seq#Length(read($Heap, this, _module.Iter0.us));
    assume $IsGoodHeap($Heap);
    call $YieldHavoc(this, _module.Iter0.__reads(this), read($Heap, this, _module.Iter0.__new));
    $_OldIterHeap := $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(31,10)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(32,3)
    assume true;
    assert LitInt(0) <= _module.Iter0.z(this);
}



const unique class._module.I1?: ClassName;

function Tclass._module.I1?() : Ty;

const unique Tagclass._module.I1?: TyTag;

// Tclass._module.I1? Tag
axiom Tag(Tclass._module.I1?()) == Tagclass._module.I1?
   && TagFamily(Tclass._module.I1?()) == tytagFamily$I1;

// Box/unbox axiom for Tclass._module.I1?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.I1?()) } 
  $IsBox(bx, Tclass._module.I1?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.I1?()));

// I1: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.I1?()) } 
  $Is($o, Tclass._module.I1?())
     <==> $o == null || dtype($o) == Tclass._module.I1?());

// I1: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.I1?(), $h) } 
  $IsAlloc($o, Tclass._module.I1?(), $h) <==> $o == null || read($h, $o, alloc));

function _module.I1.c(ref) : ref;

// I1.c: Type axiom
axiom (forall $o: ref :: 
  { _module.I1.c($o) } 
  $o != null && dtype($o) == Tclass._module.I1?()
     ==> $Is(_module.I1.c($o), Tclass._module.C()));

// I1.c: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.I1.c($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.I1.c($o), Tclass._module.C(), $h));

function _module.I1.d(ref) : ref;

// I1.d: Type axiom
axiom (forall $o: ref :: 
  { _module.I1.d($o) } 
  $o != null && dtype($o) == Tclass._module.I1?()
     ==> $Is(_module.I1.d($o), Tclass._module.C()));

// I1.d: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.I1.d($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.I1.d($o), Tclass._module.C(), $h));

function _module.I1.u(ref) : int;

// I1.u: Type axiom
axiom (forall $o: ref :: 
  { _module.I1.u($o) } 
  $o != null && dtype($o) == Tclass._module.I1?() ==> $Is(_module.I1.u($o), TInt));

// I1.u: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.I1.u($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.I1.u($o), TInt, $h));

function _module.I1.__reads(ref) : Set Box;

// I1._reads: Type axiom
axiom (forall $o: ref :: 
  { _module.I1.__reads($o) } 
  $o != null && dtype($o) == Tclass._module.I1?()
     ==> $Is(_module.I1.__reads($o), TSet(Tclass._System.object?())));

// I1._reads: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.I1.__reads($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.I1.__reads($o), TSet(Tclass._System.object?()), $h));

function _module.I1.__modifies(ref) : Set Box;

// I1._modifies: Type axiom
axiom (forall $o: ref :: 
  { _module.I1.__modifies($o) } 
  $o != null && dtype($o) == Tclass._module.I1?()
     ==> $Is(_module.I1.__modifies($o), TSet(Tclass._System.object?())));

// I1._modifies: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.I1.__modifies($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.I1.__modifies($o), TSet(Tclass._System.object?()), $h));

axiom FDim(_module.I1.__new) == 0
   && FieldOfDecl(class._module.I1?, field$_new) == _module.I1.__new
   && $IsGhostField(_module.I1.__new);

const _module.I1.__new: Field (Set Box);

// I1._new: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.I1.__new) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.I1?()
     ==> $Is(read($h, $o, _module.I1.__new), TSet(Tclass._System.object?())));

// I1._new: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.I1.__new) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.I1.__new), TSet(Tclass._System.object?()), $h));

function _module.I1.__decreases0(ref) : ref;

// I1._decreases0: Type axiom
axiom (forall $o: ref :: 
  { _module.I1.__decreases0($o) } 
  $o != null && dtype($o) == Tclass._module.I1?()
     ==> $Is(_module.I1.__decreases0($o), Tclass._module.C?()));

// I1._decreases0: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.I1.__decreases0($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.I1.__decreases0($o), Tclass._module.C?(), $h));

function _module.I1.__decreases1(ref) : ref;

// I1._decreases1: Type axiom
axiom (forall $o: ref :: 
  { _module.I1.__decreases1($o) } 
  $o != null && dtype($o) == Tclass._module.I1?()
     ==> $Is(_module.I1.__decreases1($o), Tclass._module.C?()));

// I1._decreases1: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.I1.__decreases1($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.I1.__decreases1($o), Tclass._module.C?(), $h));

function _module.I1.__decreases2(ref) : int;

// I1._decreases2: Type axiom
axiom (forall $o: ref :: 
  { _module.I1.__decreases2($o) } 
  $o != null && dtype($o) == Tclass._module.I1?()
     ==> $Is(_module.I1.__decreases2($o), TInt));

// I1._decreases2: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { _module.I1.__decreases2($o), read($h, $o, alloc) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.I1?()
       && read($h, $o, alloc)
     ==> $IsAlloc(_module.I1.__decreases2($o), TInt, $h));

function Tclass._module.I1() : Ty;

const unique Tagclass._module.I1: TyTag;

// Tclass._module.I1 Tag
axiom Tag(Tclass._module.I1()) == Tagclass._module.I1
   && TagFamily(Tclass._module.I1()) == tytagFamily$I1;

// Box/unbox axiom for Tclass._module.I1
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.I1()) } 
  $IsBox(bx, Tclass._module.I1())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.I1()));

procedure CheckWellformed$$_module.I1.__ctor(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.I1())
         && $IsAlloc(this, Tclass._module.I1(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.C()) && $IsAlloc(d#0, Tclass._module.C(), $Heap), 
    u#0: int);
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.I1.__ctor(this: ref, c#0: ref, d#0: ref, u#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: _ctor, CheckWellformed$$_module.I1.__ctor
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(151,9): initial state"} true;
    assume c#0 != d#0;
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.g) == u#0;
    assert d#0 != null;
    assume read($Heap, d#0, _module.C.g) == u#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
    assume $HeapSucc(old($Heap), $Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(151,12): post-state"} true;
    assume _module.I1.c(this) == c#0;
    assume _module.I1.d(this) == d#0;
    assume _module.I1.u(this) == u#0;
    assume _module.I1.Valid#canCall($Heap, this);
    assume _module.I1.Valid($Heap, this);
    assume Set#Equal(_module.I1.__reads(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(_module.I1.__modifies(this), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), $Box(d#0)));
    assume Set#Equal(read($Heap, this, _module.I1.__new), Set#Empty(): Set Box);
    assume _module.I1.__decreases0(this) == c#0;
    assume _module.I1.__decreases1(this) == d#0;
    assume _module.I1.__decreases2(this) == u#0;
}



procedure Call$$_module.I1.__ctor(c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.C()) && $IsAlloc(d#0, Tclass._module.C(), $Heap), 
    u#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.I1())
         && $IsAlloc(this, Tclass._module.I1(), $Heap));
  // user-defined preconditions
  requires c#0 != d#0;
  requires read($Heap, c#0, _module.C.g) == u#0;
  requires read($Heap, d#0, _module.C.g) == u#0;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures _module.I1.c(this) == c#0;
  free ensures true;
  ensures _module.I1.d(this) == d#0;
  free ensures true;
  ensures _module.I1.u(this) == u#0;
  free ensures _module.I1.Valid#canCall($Heap, this);
  ensures _module.I1.Valid($Heap, this);
  free ensures true;
  ensures Set#Equal(_module.I1.__reads(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
  free ensures true;
  ensures Set#Equal(_module.I1.__modifies(this), 
    Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), $Box(d#0)));
  free ensures true;
  ensures Set#Equal(read($Heap, this, _module.I1.__new), Set#Empty(): Set Box);
  free ensures true;
  ensures _module.I1.__decreases0(this) == c#0;
  free ensures true;
  ensures _module.I1.__decreases1(this) == d#0;
  free ensures true;
  ensures _module.I1.__decreases2(this) == u#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// function declaration for _module.I1.Valid
function _module.I1.Valid($heap: Heap, this: ref) : bool;

function _module.I1.Valid#canCall($heap: Heap, this: ref) : bool;

// frame axiom for _module.I1.Valid
axiom (forall $h0: Heap, $h1: Heap, this: ref :: 
  { $IsHeapAnchor($h0), $HeapSucc($h0, $h1), _module.I1.Valid($h1, this) } 
  $IsGoodHeap($h0)
       && $IsGoodHeap($h1)
       && 
      this != null
       && $Is(this, Tclass._module.I1())
       && 
      $IsHeapAnchor($h0)
       && $HeapSucc($h0, $h1)
     ==> 
    (forall<alpha> $o: ref, $f: Field alpha :: 
      $o != null
           && (
            $o == this
             || _module.I1.__reads(this)[$Box($o)]
             || read($h0, this, _module.I1.__new)[$Box($o)])
         ==> read($h0, $o, $f) == read($h1, $o, $f))
     ==> _module.I1.Valid($h0, this) == _module.I1.Valid($h1, this));

// consequence axiom for _module.I1.Valid
axiom 11 <= $FunctionContextHeight
   ==> (forall $Heap: Heap, this: ref :: 
    { _module.I1.Valid($Heap, this) } 
    _module.I1.Valid#canCall($Heap, this)
         || (11 != $FunctionContextHeight
           && 
          $IsGoodHeap($Heap)
           && 
          this != null
           && 
          $Is(this, Tclass._module.I1())
           && $IsAlloc(this, Tclass._module.I1(), $Heap))
       ==> true);

function _module.I1.Valid#requires(Heap, ref) : bool;

// #requires axiom for _module.I1.Valid
axiom (forall $Heap: Heap, this: ref :: 
  { _module.I1.Valid#requires($Heap, this), $IsGoodHeap($Heap) } 
  $IsGoodHeap($Heap)
       && 
      this != null
       && 
      $Is(this, Tclass._module.I1())
       && $IsAlloc(this, Tclass._module.I1(), $Heap)
     ==> _module.I1.Valid#requires($Heap, this) == true);

procedure CheckWellformed$$_module.I1.Valid(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.I1())
         && $IsAlloc(this, Tclass._module.I1(), $Heap));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.I1.Valid(this: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;

    b$reqreads#0 := true;

    // AddWellformednessCheck for function Valid
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(151,9): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc)
         ==> $o == this
           || _module.I1.__reads(this)[$Box($o)]
           || read($Heap, this, _module.I1.__new)[$Box($o)]);
    b$reqreads#0 := $_Frame[this, _module.I1.__new];
    assert b$reqreads#0;
    if (*)
    {
        assume false;
    }
    else
    {
        assume false;
    }
}



procedure Call$$_module.I1.MoveNext(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.I1())
         && $IsAlloc(this, Tclass._module.I1(), $Heap))
   returns (more#0: bool);
  // user-defined preconditions
  requires _module.I1.Valid($Heap, this);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures (forall $o: ref :: 
    { read(old($Heap), $o, alloc) } 
    read($Heap, this, _module.I1.__new)[$Box($o)]
         && !read(old($Heap), this, _module.I1.__new)[$Box($o)]
       ==> $o != null && !read(old($Heap), $o, alloc));
  free ensures true;
  ensures !read($Heap, this, _module.I1.__new)[$Box(null)];
  free ensures more#0 ==> _module.I1.Valid#canCall($Heap, this);
  ensures more#0 ==> _module.I1.Valid($Heap, this);
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o]
         || 
        $o == this
         || _module.I1.__modifies(this)[$Box($o)]
         || read(old($Heap), this, _module.I1.__new)[$Box($o)]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



// _module.I1: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.I1()) } 
  $Is(c#0, Tclass._module.I1()) <==> $Is(c#0, Tclass._module.I1?()) && c#0 != null);

// _module.I1: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.I1(), $h) } 
  $IsAlloc(c#0, Tclass._module.I1(), $h)
     <==> $IsAlloc(c#0, Tclass._module.I1?(), $h));

procedure CheckWellformed$$_module.I1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.I1())
         && $IsAlloc(this, Tclass._module.I1(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.C()) && $IsAlloc(d#0, Tclass._module.C(), $Heap), 
    u#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.I1(this: ref, c#0: ref, d#0: ref, u#0: int)
{
  var $_OldIterHeap: Heap;

    assume c#0 != d#0;
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.g) == u#0;
    assert d#0 != null;
    assume read($Heap, d#0, _module.C.g) == u#0;
    assume _module.I1.c(this) == c#0;
    assume _module.I1.d(this) == d#0;
    assume _module.I1.u(this) == u#0;
    assume _module.I1.Valid($Heap, this);
    assume Set#Equal(_module.I1.__reads(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(_module.I1.__modifies(this), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), $Box(d#0)));
    assume Set#Equal(read($Heap, this, _module.I1.__new), Set#Empty(): Set Box);
    assume _module.I1.__decreases0(this) == c#0;
    assume _module.I1.__decreases1(this) == d#0;
    assume _module.I1.__decreases2(this) == u#0;
    call $IterHavoc0(this, _module.I1.__reads(this), _module.I1.__modifies(this));
    assume _module.I1.Valid($Heap, this);
    $_OldIterHeap := $Heap;
    call $IterHavoc1(this, _module.I1.__modifies(this), read($Heap, this, _module.I1.__new));
    assume (forall $o: ref :: 
      { read($_OldIterHeap, $o, alloc) } 
      read($Heap, this, _module.I1.__new)[$Box($o)]
           && !read($_OldIterHeap, this, _module.I1.__new)[$Box($o)]
         ==> $o != null && !read($_OldIterHeap, $o, alloc));
    if (*)
    {
        assume _module.I1.Valid($Heap, this);
    }
    else
    {
    }
}



procedure Impl$$_module.I1(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.I1())
         && $IsAlloc(this, Tclass._module.I1(), $Heap), 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap), 
    d#0: ref
       where $Is(d#0, Tclass._module.C()) && $IsAlloc(d#0, Tclass._module.C(), $Heap), 
    u#0: int);
  free requires 1 == $FunctionContextHeight;
  // user-defined preconditions
  requires c#0 != d#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0 || $o == d#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.I1(this: ref, c#0: ref, d#0: ref, u#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _yieldCount#0: int where true;
  var $_OldIterHeap: Heap
     where $IsGoodHeap($_OldIterHeap) && $HeapSucc($_OldIterHeap, $Heap);
  var v#0: int;
  var $Heap_at_0: Heap;
  var ##$Heap_at_0#v#0: int;
  var $Heap_at_1: Heap;
  var ##$Heap_at_1#v#0: int;
  var $rhs#0: int;
  var $Heap_at_2: Heap;
  var ##$Heap_at_2#v#0: int;
  var vv#0: int;
  var $Heap_at_3: Heap;
  var ##$Heap_at_3#v#0: int;
  var $obj1: ref;
  var $rhs#1: int;
  var $rhs#2: int;

    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == this || $o == c#0 || $o == d#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(151,9): initial state"} true;
    assume c#0 != d#0;
    assume _module.I1.c(this) == c#0;
    assume _module.I1.d(this) == d#0;
    assume _module.I1.u(this) == u#0;
    assume _module.I1.Valid($Heap, this);
    assume Set#Equal(_module.I1.__reads(this), Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)));
    assume Set#Equal(_module.I1.__modifies(this), 
      Set#UnionOne(Set#UnionOne(Set#Empty(): Set Box, $Box(c#0)), $Box(d#0)));
    assume Set#Equal(read($Heap, this, _module.I1.__new), Set#Empty(): Set Box);
    assume _module.I1.__decreases0(this) == c#0;
    assume _module.I1.__decreases1(this) == d#0;
    assume _module.I1.__decreases2(this) == u#0;
    assume _yieldCount#0 == 0;
    call $YieldHavoc(this, _module.I1.__reads(this), read($Heap, this, _module.I1.__new));
    $_OldIterHeap := $Heap;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(158,9)
    assume true;
    assume true;
    v#0 := _module.I1.u(this);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(158,12)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(159,3)
    assert {:subsumption 0} _module.I1.c(this) != null;
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(159,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(160,5)
        assume read(old($Heap), c#0, _module.C.g) == u#0;
        assert read($Heap, _module.I1.c(this), _module.C.g) == v#0;
        assume false;
    }

    $Heap_at_0 := $Heap;
    ##$Heap_at_0#v#0 := v#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(162,3)
    assert {:subsumption 0} _module.I1.d(this) != null;
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(162,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(163,5)
        assume read(old($Heap), d#0, _module.C.g) == u#0;
        assert read($Heap, _module.I1.d(this), _module.C.g) == v#0;
        assume false;
    }

    $Heap_at_1 := $Heap;
    ##$Heap_at_1#v#0 := v#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(165,7)
    assert _module.I1.c(this) != null;
    assume true;
    assert $_Frame[_module.I1.c(this), _module.C.g];
    assert _module.I1.c(this) != null;
    assume true;
    $rhs#0 := read($Heap, _module.I1.c(this), _module.C.g) + 2;
    $Heap := update($Heap, _module.I1.c(this), _module.C.g, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(165,16)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(166,3)
    assert {:subsumption 0} _module.I1.c(this) != null;
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(166,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(167,5)
        assume read($Heap_at_0, _module.I1.c(this), _module.C.g) == ##$Heap_at_0#v#0;
        assert read($Heap, _module.I1.c(this), _module.C.g) == v#0 + 2;
        assume false;
    }

    $Heap_at_2 := $Heap;
    ##$Heap_at_2#v#0 := v#0;
    // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(169,3)
    _yieldCount#0 := _yieldCount#0 + 1;
    assume true;
    assume $IsGoodHeap($Heap);
    call $YieldHavoc(this, _module.I1.__reads(this), read($Heap, this, _module.I1.__new));
    $_OldIterHeap := $Heap;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(169,7)"} true;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(170,3)
    if (*)
    {
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(171,5)
        assume read(old($Heap), c#0, _module.C.g) == u#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(172,5)
        assert {:subsumption 0} _module.I1.c(this) != null;
        assume true;
        assert read($Heap, _module.I1.c(this), _module.C.g) == _module.I1.u(this);
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(173,10)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(174,7)
            assume true;
            assume true;
            v#0 := v#0 + 3;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(174,14)"} true;
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(175,5)
            assume read($Heap_at_0, _module.I1.c(this), _module.C.g) == ##$Heap_at_0#v#0;
            // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(176,5)
            _yieldCount#0 := _yieldCount#0 + 1;
            assume true;
            assume $IsGoodHeap($Heap);
            call $YieldHavoc(this, _module.I1.__reads(this), read($Heap, this, _module.I1.__new));
            $_OldIterHeap := $Heap;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(176,9)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(177,5)
            assert {:subsumption 0} _module.I1.c(this) != null;
            assume true;
            assert v#0 - 1 == read($Heap, _module.I1.c(this), _module.C.g);
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(179,7)
            assume true;
            assume true;
            v#0 := v#0 + 5;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(179,14)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(180,12)
            assume true;
            assume true;
            vv#0 := v#0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(180,15)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(181,5)
            assert {:subsumption 0} _module.I1.c(this) != null;
            assume true;
            if (*)
            {
                // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(181,5)
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(182,7)
                assume read($Heap_at_0, _module.I1.c(this), _module.C.g) == ##$Heap_at_0#v#0;
                assert v#0 - 3 == read($Heap, _module.I1.c(this), _module.C.g);
                assume false;
            }

            $Heap_at_3 := $Heap;
            ##$Heap_at_3#v#0 := v#0;
            // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(184,5)
            _yieldCount#0 := _yieldCount#0 + 1;
            assume true;
            assume $IsGoodHeap($Heap);
            call $YieldHavoc(this, _module.I1.__reads(this), read($Heap, this, _module.I1.__new));
            $_OldIterHeap := $Heap;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(184,9)"} true;
            // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(185,12)
            assume true;
            assert _module.I1.c(this) != null;
            assume true;
            $obj1 := _module.I1.c(this);
            assert $_Frame[$obj1, _module.C.g];
            assume true;
            $rhs#1 := LitInt(178);
            assert _module.I1.c(this) != null;
            assume true;
            $rhs#2 := read($Heap, _module.I1.c(this), _module.C.g) + 100;
            v#0 := $rhs#1;
            $Heap := update($Heap, $obj1, _module.C.g, $rhs#2);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(185,28)"} true;
            // ----- yield statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(186,5)
            _yieldCount#0 := _yieldCount#0 + 1;
            assume true;
            assume $IsGoodHeap($Heap);
            call $YieldHavoc(this, _module.I1.__reads(this), read($Heap, this, _module.I1.__new));
            $_OldIterHeap := $Heap;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(186,9)"} true;
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(187,5)
            if (*)
            {
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(188,7)
                assume ##$Heap_at_3#v#0 - 3 == read($Heap_at_3, _module.I1.c(this), _module.C.g);
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(189,7)
                assert {:subsumption 0} _module.I1.c(this) != null;
                assume true;
                assert v#0 - 3 == read($Heap, _module.I1.c(this), _module.C.g);
            }
            else
            {
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(191,7)
                assume ##$Heap_at_3#v#0 - 3 == read($Heap_at_3, _module.I1.c(this), _module.C.g);
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(192,7)
                assert $IsAlloc(this, Tclass._module.I1(), $Heap_at_3);
                assert {:subsumption 0} _module.I1.c(this) != null;
                assert $IsAlloc(_module.I1.c(this), Tclass._module.C(), $Heap_at_3);
                assume true;
                assert read($Heap_at_3, _module.I1.c(this), _module.C.g) == vv#0 - 3;
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(193,7)
                assume true;
                assert false;
            }
        }
    }
}



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

procedure CheckWellformed$$_module.__default.M0(x#0: int, y#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M0(x#0: int, y#0: int);
  // user-defined preconditions
  requires LitInt(0) <= x#0;
  requires LitInt(0) <= y#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M0(x#0: int, y#0: int) returns ($_reverifyPost: bool);
  free requires 14 == $FunctionContextHeight;
  // user-defined preconditions
  requires LitInt(0) <= x#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M0(x#0: int, y#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M0, Impl$$_module.__default.M0
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(14,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(15,3)
    assume true;
    assert LitInt(0) <= x#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(16,3)
    assume true;
    assert LitInt(0) <= y#0;
}



procedure CheckWellformed$$_module.__default.T0(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap));
  free requires 2 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.T0(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T0, CheckWellformed$$_module.__default.T0
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(35,15): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume read(old($Heap), c#0, _module.C.g) == LitInt(10);
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.g) == LitInt(20);
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume read(old($Heap), c#0, _module.C.h) == LitInt(100);
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.h) == LitInt(200);
}



procedure Call$$_module.__default.T0(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap));
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, _module.C.g) == LitInt(10);
  requires read(current$Heap, c#0, _module.C.g) == LitInt(20);
  requires read(previous$Heap, c#0, _module.C.h) == LitInt(100);
  requires read(current$Heap, c#0, _module.C.h) == LitInt(200);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.T0(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, _module.C.g) == LitInt(10);
  requires read(current$Heap, c#0, _module.C.g) == LitInt(20);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.T0(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T0, Impl$$_module.__default.T0
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(40,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(41,3)
    assert {:subsumption 0} c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assert {:subsumption 0} c#0 != null;
    assume true;
    assert read(old($Heap), c#0, _module.C.g) < read($Heap, c#0, _module.C.g);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(42,3)
    assert {:subsumption 0} c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume true;
    assert read(old($Heap), c#0, _module.C.h) < 150;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(43,3)
    assert {:subsumption 0} c#0 != null;
    assume true;
    assert 150 < read($Heap, c#0, _module.C.h);
}



procedure CheckWellformed$$_module.__default.Test(c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap));
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.Test(c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: Test, CheckWellformed$$_module.__default.Test
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(46,7): initial state"} true;
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.g) == LitInt(0);
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.Test(c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap));
  // user-defined preconditions
  requires read($Heap, c#0, _module.C.g) == LitInt(0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Test(c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap))
   returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
  // user-defined preconditions
  requires read($Heap, c#0, _module.C.g) == LitInt(0);
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Test(c#0: ref) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var local#0: int;
  var $rhs#0: int;
  var $Heap_at_0: Heap;
  var $Heap_at_1: Heap;
  var $Heap_at_2: Heap;
  var ##$Heap_at_2#local#0: int;
  var $obj1: ref;
  var $rhs#1: int;
  var $rhs#2: int;
  var $Heap_at_3: Heap;
  var $Heap_at_4: Heap;
  var $Heap_at_5: Heap;
  var ##$Heap_at_5#local#0: int;
  var $rhs#3: int;
  var $rhs#4: int;
  var $Heap_at_6: Heap;
  var ##$Heap_at_6#local#0: int;

    // AddMethodImpl: Test, Impl$$_module.__default.Test
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(49,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(50,13)
    assume true;
    assume true;
    local#0 := LitInt(1);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(50,16)"} true;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(51,7)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, _module.C.g];
    assume true;
    $rhs#0 := local#0;
    $Heap := update($Heap, c#0, _module.C.g, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(51,14)"} true;
    $Heap_at_0 := $Heap;
    $Heap_at_1 := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(53,3)
    assert {:subsumption 0} c#0 != null;
    if (read($Heap, c#0, _module.C.g) == local#0)
    {
    }

    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(53,3)
        assert {:subsumption 0} read($Heap, c#0, _module.C.g) == local#0;
        assert {:subsumption 0} local#0 == LitInt(1);
        assume false;
    }

    $Heap_at_2 := $Heap;
    ##$Heap_at_2#local#0 := local#0;

  after_0:
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(55,14)
    assume true;
    assert c#0 != null;
    assume true;
    $obj1 := c#0;
    assert $_Frame[$obj1, _module.C.g];
    assume true;
    $rhs#1 := local#0 + 1;
    assume true;
    $rhs#2 := local#0 + 1;
    local#0 := $rhs#1;
    $Heap := update($Heap, $obj1, _module.C.g, $rhs#2);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(55,36)"} true;
    $Heap_at_3 := $Heap;
    $Heap_at_4 := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(57,3)
    assert {:subsumption 0} c#0 != null;
    if (read($Heap, c#0, _module.C.g) == local#0)
    {
    }

    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(57,3)
        assert {:subsumption 0} read($Heap, c#0, _module.C.g) == local#0;
        assert {:subsumption 0} local#0 == LitInt(2);
        assume false;
    }

    $Heap_at_5 := $Heap;
    ##$Heap_at_5#local#0 := local#0;

  after_3:
    // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(59,14)
    assume true;
    assert c#0 != null;
    assume true;
    $obj1 := c#0;
    assert $_Frame[$obj1, _module.C.g];
    assume true;
    $rhs#3 := local#0 + 1;
    assume true;
    $rhs#4 := local#0 + 1;
    local#0 := $rhs#3;
    $Heap := update($Heap, $obj1, _module.C.g, $rhs#4);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(59,36)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(60,3)
    assert {:subsumption 0} c#0 != null;
    if (read($Heap, c#0, _module.C.g) == local#0)
    {
    }

    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(60,3)
        assert {:subsumption 0} read($Heap, c#0, _module.C.g) == local#0;
        assert {:subsumption 0} local#0 == LitInt(3);
        assume false;
    }

    $Heap_at_6 := $Heap;
    ##$Heap_at_6#local#0 := local#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(62,3)
    assert {:subsumption 0} c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assert {:subsumption 0} c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), $Heap_at_0);
    if (read(old($Heap), c#0, _module.C.g) < read($Heap_at_0, c#0, _module.C.g))
    {
        assert {:subsumption 0} c#0 != null;
        assert $IsAlloc(c#0, Tclass._module.C(), $Heap_at_0);
        assert {:subsumption 0} c#0 != null;
        assert $IsAlloc(c#0, Tclass._module.C(), $Heap_at_3);
    }

    if (read(old($Heap), c#0, _module.C.g) < read($Heap_at_0, c#0, _module.C.g)
       && read($Heap_at_0, c#0, _module.C.g) < read($Heap_at_3, c#0, _module.C.g))
    {
        assert {:subsumption 0} c#0 != null;
        assert $IsAlloc(c#0, Tclass._module.C(), $Heap_at_3);
        assert {:subsumption 0} c#0 != null;
    }

    assume true;
    assert {:subsumption 0} read(old($Heap), c#0, _module.C.g) < read($Heap_at_0, c#0, _module.C.g);
    assert {:subsumption 0} read($Heap_at_0, c#0, _module.C.g) < read($Heap_at_3, c#0, _module.C.g);
    assert {:subsumption 0} read($Heap_at_3, c#0, _module.C.g) < read($Heap, c#0, _module.C.g);
    assume read(old($Heap), c#0, _module.C.g) < read($Heap_at_0, c#0, _module.C.g)
       && read($Heap_at_0, c#0, _module.C.g) < read($Heap_at_3, c#0, _module.C.g)
       && read($Heap_at_3, c#0, _module.C.g) < read($Heap, c#0, _module.C.g);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(63,3)
    if (local#0 == LitInt(3))
    {
    }

    assume true;
    assert {:subsumption 0} local#0 == LitInt(3);
    assert {:subsumption 0} LitInt(3) == local#0;
    assume local#0 == LitInt(3) && LitInt(3) == local#0;
}



procedure CheckWellformed$$_module.__default.M1(x#0: int, y#0: int, z#0: int);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M1(x#0: int, y#0: int, z#0: int);
  // user-defined preconditions
  requires LitInt(0) <= x#0;
  requires LitInt(0) <= y#0;
  requires LitInt(0) <= z#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M1(x#0: int, y#0: int, z#0: int) returns ($_reverifyPost: bool);
  free requires 15 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M1(x#0: int, y#0: int, z#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $Heap_at_0: Heap;
  var $Heap_at_1: Heap;
  var $Heap_at_2: Heap;

    // AddMethodImpl: M1, Impl$$_module.__default.M1
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(70,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(71,3)
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(71,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(72,5)
        assume LitInt(0) <= x#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(73,5)
        assume true;
        assert LitInt(0) <= x#0;
        assert LitInt(-20) <= x#0;
        assume false;
    }

    $Heap_at_0 := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(75,3)
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(75,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(76,5)
        assume LitInt(0) <= y#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(77,5)
        assume true;
        assert LitInt(0) <= y#0;
        assert LitInt(-20) <= y#0;
        assume false;
    }

    $Heap_at_1 := $Heap;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(79,3)
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(79,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(80,5)
        assume LitInt(0) <= z#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(81,5)
        assume true;
        assert LitInt(0) <= z#0;
        assert LitInt(-20) <= z#0;
        assume false;
    }

    $Heap_at_2 := $Heap;
    // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(84,3)
    assume LitInt(-20) <= x#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(85,3)
    assume true;
    assert LitInt(-20) <= x#0;
    // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(86,3)
    assume LitInt(-20) <= y#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(87,3)
    assume true;
    assert LitInt(-20) <= y#0;
    // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(88,3)
    assume LitInt(-20) <= z#0;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(89,3)
    assume true;
    assert LitInt(-20) <= z#0;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(90,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(91,5)
        assume true;
        assert LitInt(0) <= z#0;
    }
    else
    {
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(93,5)
        assume LitInt(0) <= z#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(94,5)
        assume true;
        assert LitInt(0) <= z#0;
    }
}



procedure CheckWellformed$$_module.__default.M2(x#0: int);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.M2(x#0: int);
  // user-defined preconditions
  requires LitInt(0) <= x#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M2(x#0: int) returns ($_reverifyPost: bool);
  free requires 16 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M2(x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var x#0_0: int;

    // AddMethodImpl: M2, Impl$$_module.__default.M2
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(100,0): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(102,3)
    if (*)
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(103,11)
        assume true;
        assume true;
        x#0_0 := LitInt(-8);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(103,15)"} true;
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(104,5)
        assume LitInt(0) <= x#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(105,5)
        assume true;
        assert LitInt(0) <= x#0_0;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(106,10)
        if (*)
        {
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(107,5)
            assume true;
            assert LitInt(0) <= x#0;
        }
        else
        {
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(109,5)
            assume LitInt(0) <= x#0;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(110,5)
            assume true;
            assert LitInt(0) <= x#0;
        }
    }
}



procedure CheckWellformed$$_module.__default.M3(c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap), 
    u#0: int);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.M3(c#0: ref, u#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: M3, CheckWellformed$$_module.__default.M3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(114,7): initial state"} true;
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.g) == u#0;
    havoc $Heap;
    assume (forall $o: ref :: 
      { $Heap[$o] } 
      $o != null && read(old($Heap), $o, alloc)
         ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
    assume $HeapSucc(old($Heap), $Heap);
}



procedure Call$$_module.__default.M3(c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap), 
    u#0: int);
  // user-defined preconditions
  requires read($Heap, c#0, _module.C.g) == u#0;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.M3(c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), $Heap), 
    u#0: int)
   returns ($_reverifyPost: bool);
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc)
       ==> $Heap[$o] == old($Heap)[$o] || $o == c#0);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.M3(c#0: ref, u#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var v#0: int;
  var $Heap_at_0: Heap;
  var ##$Heap_at_0#v#0: int;
  var $rhs#0: int;
  var $Heap_at_1: Heap;
  var ##$Heap_at_1#v#0: int;
  var vv#0: int;
  var $Heap_at_2: Heap;
  var ##$Heap_at_2#v#0: int;
  var $obj1: ref;
  var $rhs#1: int;
  var $rhs#2: int;

    // AddMethodImpl: M3, Impl$$_module.__default.M3
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> $o == c#0);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(117,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(118,9)
    assume true;
    assume true;
    v#0 := u#0;
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(118,12)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(119,3)
    assert {:subsumption 0} c#0 != null;
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(119,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(120,5)
        assume read(old($Heap), c#0, _module.C.g) == u#0;
        assert read($Heap, c#0, _module.C.g) == v#0;
        assume false;
    }

    $Heap_at_0 := $Heap;
    ##$Heap_at_0#v#0 := v#0;
    // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(122,7)
    assert c#0 != null;
    assume true;
    assert $_Frame[c#0, _module.C.g];
    assert c#0 != null;
    assume true;
    $rhs#0 := read($Heap, c#0, _module.C.g) + 2;
    $Heap := update($Heap, c#0, _module.C.g, $rhs#0);
    assume $IsGoodHeap($Heap);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(122,16)"} true;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(123,3)
    assert {:subsumption 0} c#0 != null;
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(123,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(124,5)
        assume read($Heap_at_0, c#0, _module.C.g) == ##$Heap_at_0#v#0;
        assert read($Heap, c#0, _module.C.g) == v#0 + 2;
        assume false;
    }

    $Heap_at_1 := $Heap;
    ##$Heap_at_1#v#0 := v#0;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(126,3)
    if (*)
    {
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(127,5)
        assume read(old($Heap), c#0, _module.C.g) == u#0;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(128,5)
        assert {:subsumption 0} c#0 != null;
        assume true;
        assert read($Heap, c#0, _module.C.g) == u#0;
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(129,10)
        if (*)
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(130,7)
            assume true;
            assume true;
            v#0 := v#0 + 3;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(130,14)"} true;
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(131,5)
            assume read($Heap_at_0, c#0, _module.C.g) == ##$Heap_at_0#v#0;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(132,5)
            assert {:subsumption 0} c#0 != null;
            assume true;
            assert v#0 - 1 == read($Heap, c#0, _module.C.g);
        }
        else
        {
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(134,7)
            assume true;
            assume true;
            v#0 := v#0 + 5;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(134,14)"} true;
            // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(135,12)
            assume true;
            assume true;
            vv#0 := v#0;
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(135,15)"} true;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(136,5)
            assert {:subsumption 0} c#0 != null;
            assume true;
            if (*)
            {
                // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(136,5)
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(137,7)
                assume read($Heap_at_0, c#0, _module.C.g) == ##$Heap_at_0#v#0;
                assert v#0 - 3 == read($Heap, c#0, _module.C.g);
                assume false;
            }

            $Heap_at_2 := $Heap;
            ##$Heap_at_2#v#0 := v#0;
            // ----- update statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(139,12)
            assume true;
            assert c#0 != null;
            assume true;
            $obj1 := c#0;
            assert $_Frame[$obj1, _module.C.g];
            assume true;
            $rhs#1 := LitInt(178);
            assert c#0 != null;
            assume true;
            $rhs#2 := read($Heap, c#0, _module.C.g) + 100;
            v#0 := $rhs#1;
            $Heap := update($Heap, $obj1, _module.C.g, $rhs#2);
            assume $IsGoodHeap($Heap);
            assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(139,28)"} true;
            // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(140,5)
            if (*)
            {
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(141,7)
                assume ##$Heap_at_2#v#0 - 3 == read($Heap_at_2, c#0, _module.C.g);
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(142,7)
                assert {:subsumption 0} c#0 != null;
                assume true;
                assert v#0 - 3 == read($Heap, c#0, _module.C.g);
            }
            else
            {
                // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(144,7)
                assume ##$Heap_at_2#v#0 - 3 == read($Heap_at_2, c#0, _module.C.g);
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(145,7)
                assert {:subsumption 0} c#0 != null;
                assert $IsAlloc(c#0, Tclass._module.C(), $Heap_at_2);
                assume true;
                assert read($Heap_at_2, c#0, _module.C.g) == vv#0 - 3;
                // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(146,7)
                assume true;
                assert false;
            }
        }
    }
}



procedure CheckWellformed$$_module.__default.T1(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap));
  free requires 5 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.T1(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T1, CheckWellformed$$_module.__default.T1
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(198,15): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume read(old($Heap), c#0, _module.C.g) == LitInt(10);
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.g) == LitInt(20);
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume read(old($Heap), c#0, _module.C.h) == LitInt(100);
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.h) == LitInt(200);
}



procedure Call$$_module.__default.T1(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap));
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, _module.C.g) == LitInt(10);
  requires read(current$Heap, c#0, _module.C.g) == LitInt(20);
  requires read(previous$Heap, c#0, _module.C.h) == LitInt(100);
  requires read(current$Heap, c#0, _module.C.h) == LitInt(200);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.T1(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 5 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, _module.C.g) == LitInt(10);
  requires read(current$Heap, c#0, _module.C.g) == LitInt(20);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.T1(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T1, Impl$$_module.__default.T1
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(203,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(204,3)
    assert {:subsumption 0} c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assert {:subsumption 0} c#0 != null;
    assume true;
    assert read(old($Heap), c#0, _module.C.g) < read($Heap, c#0, _module.C.g);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(205,3)
    if (*)
    {
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(206,5)
        assert {:subsumption 0} c#0 != null;
        assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
        assume true;
        assert read(old($Heap), c#0, _module.C.h) < 150;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(207,5)
        assert {:subsumption 0} c#0 != null;
        assume true;
        assert 150 < read($Heap, c#0, _module.C.h);
    }
    else
    {
        // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(208,10)
        if (*)
        {
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(209,5)
            assume read(old($Heap), c#0, _module.C.h) == LitInt(100);
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(210,5)
            assert {:subsumption 0} c#0 != null;
            assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
            assume true;
            assert read(old($Heap), c#0, _module.C.h) < 150;
            // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(211,5)
            assert {:subsumption 0} c#0 != null;
            assume true;
            assert 150 < read($Heap, c#0, _module.C.h);
        }
        else
        {
        }
    }
}



procedure CheckWellformed$$_module.__default.T2(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap));
  free requires 6 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.T2(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T2, CheckWellformed$$_module.__default.T2
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(215,15): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume read(old($Heap), c#0, _module.C.g) == LitInt(10);
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.g) == LitInt(20);
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume read(old($Heap), c#0, _module.C.h) == LitInt(100);
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.h) == LitInt(200);
}



procedure Call$$_module.__default.T2(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap));
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, _module.C.g) == LitInt(10);
  requires read(current$Heap, c#0, _module.C.g) == LitInt(20);
  requires read(previous$Heap, c#0, _module.C.h) == LitInt(100);
  requires read(current$Heap, c#0, _module.C.h) == LitInt(200);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.T2(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 6 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, _module.C.g) == LitInt(10);
  requires read(current$Heap, c#0, _module.C.g) == LitInt(20);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.T2(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T2, Impl$$_module.__default.T2
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(220,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(221,3)
    assert {:subsumption 0} c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assert {:subsumption 0} c#0 != null;
    assume true;
    assert read(old($Heap), c#0, _module.C.g) < read($Heap, c#0, _module.C.g);
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(222,3)
    if (*)
    {
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(223,5)
        assume read($Heap, c#0, _module.C.h) == LitInt(200);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(224,5)
        assert {:subsumption 0} c#0 != null;
        assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
        assume true;
        assert read(old($Heap), c#0, _module.C.h) < 150;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(225,5)
        assert {:subsumption 0} c#0 != null;
        assume true;
        assert 150 < read($Heap, c#0, _module.C.h);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(226,5)
        assume true;
        assert false;
    }
    else
    {
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(228,5)
        assume read(old($Heap), c#0, _module.C.h) == LitInt(100);
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(229,5)
        assume read($Heap, c#0, _module.C.h) == LitInt(200);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(230,5)
        assert {:subsumption 0} c#0 != null;
        assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
        assume true;
        assert read(old($Heap), c#0, _module.C.h) < 150;
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(231,5)
        assert {:subsumption 0} c#0 != null;
        assume true;
        assert 150 < read($Heap, c#0, _module.C.h);
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(232,5)
        assume true;
        assert false;
    }
}



procedure CheckWellformed$$_module.__default.Calc(x#0: int);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Calc(x#0: int);
  // user-defined preconditions
  requires x#0 < 10;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.Calc(x#0: int) returns ($_reverifyPost: bool);
  free requires 17 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.Calc(x#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var $Heap_at_0: Heap;
  var $Heap_at_0_2_0: Heap;

    // AddMethodImpl: Calc, Impl$$_module.__default.Calc
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(238,0): initial state"} true;
    $_reverifyPost := false;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(239,3)
    assume true;
    if (*)
    {
        // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(239,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(239,26)
        assume x#0 < 10;
        assert x#0 < 150;
        assume false;
    }

    $Heap_at_0 := $Heap;
    // ----- calc statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
    // Assume Fuel Constant
    if (*)
    {
        // ----- assert wf[initial] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        // ----- Hint0 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(243,9)
        assume x#0 < 150;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        // ----- assert line0 == line1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assert {:subsumption 0} (x#0 < 200) == (x#0 < 150);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        // ----- Hint1 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(245,9)
        assume true;
        if (*)
        {
            // ----- assert statement proof ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(245,9)
            // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(245,31)
            assume x#0 < 10;
            assert x#0 < 90;
            assume false;
        }

        $Heap_at_0_2_0 := $Heap;
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(246,9)
        assume x#0 < 90;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        // ----- assert line1 == line2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assert {:subsumption 0} (x#0 < 150) == (x#0 < 100);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        // ----- Hint2 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(249,9)
        assume x#0 < 10;
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        // ----- assert line2 == line3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assert {:subsumption 0} (x#0 < 100) == (x#0 < 10);
        assume false;
    }
    else if (*)
    {
        // ----- assume wf[lhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        // ----- Hint3 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        // ----- assert wf[rhs] ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assume true;
        // ----- assert line3 == line4 ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(241,3)
        assert {:subsumption 0} (x#0 < 10) == (x#0 < 100);
        assume false;
    }

    assume (x#0 < 200) == (x#0 < 100);
}



procedure CheckWellformed$$_module.__default.T3(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap));
  free requires 7 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  modifies $Heap, $Tick;



implementation CheckWellformed$$_module.__default.T3(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T3, CheckWellformed$$_module.__default.T3
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(256,15): initial state"} true;
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume read(old($Heap), c#0, _module.C.g) == LitInt(10);
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.g) == LitInt(20);
    assert c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume read(old($Heap), c#0, _module.C.h) == LitInt(100);
    assert c#0 != null;
    assume read($Heap, c#0, _module.C.h) == LitInt(200);
}



procedure Call$$_module.__default.T3(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap));
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, _module.C.g) == LitInt(10);
  requires read(current$Heap, c#0, _module.C.g) == LitInt(20);
  requires read(previous$Heap, c#0, _module.C.h) == LitInt(100);
  requires read(current$Heap, c#0, _module.C.h) == LitInt(200);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



procedure Impl$$_module.__default.T3(previous$Heap: Heap, 
    current$Heap: Heap, 
    c#0: ref
       where $Is(c#0, Tclass._module.C()) && $IsAlloc(c#0, Tclass._module.C(), previous$Heap))
   returns ($_reverifyPost: bool);
  free requires 7 == $FunctionContextHeight;
  free requires previous$Heap == $Heap
     && 
    $HeapSucc(previous$Heap, current$Heap)
     && $IsGoodHeap(current$Heap);
  requires $IsAlloc(c#0, Tclass._module.C(), previous$Heap);
  // user-defined preconditions
  requires read(previous$Heap, c#0, _module.C.g) == LitInt(10);
  requires read(current$Heap, c#0, _module.C.g) == LitInt(20);
  modifies $Heap, $Tick;
  // frame condition
  free ensures old($Heap) == $Heap;



implementation Impl$$_module.__default.T3(previous$Heap: Heap, current$Heap: Heap, c#0: ref)
   returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

    // AddMethodImpl: T3, Impl$$_module.__default.T3
    $Heap := current$Heap;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(261,0): initial state"} true;
    $_reverifyPost := false;
    // ----- reveal statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(262,3)
    assume read(old($Heap), c#0, _module.C.h) == LitInt(100);
    assume read($Heap, c#0, _module.C.h) == LitInt(200);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(263,3)
    assert {:subsumption 0} c#0 != null;
    assert $IsAlloc(c#0, Tclass._module.C(), old($Heap));
    assume true;
    assert read(old($Heap), c#0, _module.C.h) < 150;
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(264,3)
    assert {:subsumption 0} c#0 != null;
    assume true;
    assert 150 < read($Heap, c#0, _module.C.h);
    // ----- assert statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/LabeledAsserts.dfy(265,3)
    assume true;
    assert false;
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

const unique tytagFamily$_tuple#2: TyTagFamily;

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$C: TyTagFamily;

const unique tytagFamily$Iter0: TyTagFamily;

const unique tytagFamily$I1: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;

const unique field$g: NameFamily;

const unique field$h: NameFamily;

const unique field$u: NameFamily;

const unique field$us: NameFamily;

const unique field$_new: NameFamily;
