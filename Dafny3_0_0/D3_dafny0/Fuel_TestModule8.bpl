// Dafny 3.0.0.30204
// Command Line Options: -compile:0 -noVerify /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy -print:./Fuel.bpl

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

const BaseFuel_TestModule8._default.ValInGrammar: LayerType;

const StartFuel_TestModule8._default.ValInGrammar: LayerType;

const StartFuelAssert_TestModule8._default.ValInGrammar: LayerType;

procedure CheckWellformed$$TestModule8.byte(i#0: int);
  free requires 14 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.byte(i#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype byte
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(295,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(0) <= i#0)
        {
        }

        assume LitInt(0) <= i#0 && i#0 < 256;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(0) <= LitInt(0);
        assert {:subsumption 0} 0 < 256;
    }
}



function Tclass.TestModule8.byte() : Ty;

const unique Tagclass.TestModule8.byte: TyTag;

// Tclass.TestModule8.byte Tag
axiom Tag(Tclass.TestModule8.byte()) == Tagclass.TestModule8.byte
   && TagFamily(Tclass.TestModule8.byte()) == tytagFamily$byte;

// Box/unbox axiom for Tclass.TestModule8.byte
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TestModule8.byte()) } 
  $IsBox(bx, Tclass.TestModule8.byte())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass.TestModule8.byte()));

// TestModule8.byte: newtype $Is
axiom (forall i#0: int :: 
  { $Is(i#0, Tclass.TestModule8.byte()) } 
  $Is(i#0, Tclass.TestModule8.byte()) <==> LitInt(0) <= i#0 && i#0 < 256);

// TestModule8.byte: newtype $IsAlloc
axiom (forall i#0: int, $h: Heap :: 
  { $IsAlloc(i#0, Tclass.TestModule8.byte(), $h) } 
  $IsAlloc(i#0, Tclass.TestModule8.byte(), $h));

const unique class.TestModule8.byte: ClassName;

procedure CheckWellformed$$TestModule8.uint64(i#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.uint64(i#0: int)
{
  var $_Frame: <beta>[ref,Field beta]bool;


    // AddWellformednessCheck for newtype uint64
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(296,12): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    if (*)
    {
        if (LitInt(0) <= i#0)
        {
        }

        assume LitInt(0) <= i#0 && i#0 < 18446744073709551616;
    }
    else
    {
        assume true;
        assert {:subsumption 0} LitInt(0) <= LitInt(0);
        assert {:subsumption 0} 0 < 18446744073709551616;
    }
}



function Tclass.TestModule8.uint64() : Ty;

const unique Tagclass.TestModule8.uint64: TyTag;

// Tclass.TestModule8.uint64 Tag
axiom Tag(Tclass.TestModule8.uint64()) == Tagclass.TestModule8.uint64
   && TagFamily(Tclass.TestModule8.uint64()) == tytagFamily$uint64;

// Box/unbox axiom for Tclass.TestModule8.uint64
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TestModule8.uint64()) } 
  $IsBox(bx, Tclass.TestModule8.uint64())
     ==> $Box($Unbox(bx): int) == bx && $Is($Unbox(bx): int, Tclass.TestModule8.uint64()));

// TestModule8.uint64: newtype $Is
axiom (forall i#0: int :: 
  { $Is(i#0, Tclass.TestModule8.uint64()) } 
  $Is(i#0, Tclass.TestModule8.uint64())
     <==> LitInt(0) <= i#0 && i#0 < 18446744073709551616);

// TestModule8.uint64: newtype $IsAlloc
axiom (forall i#0: int, $h: Heap :: 
  { $IsAlloc(i#0, Tclass.TestModule8.uint64(), $h) } 
  $IsAlloc(i#0, Tclass.TestModule8.uint64(), $h));

const unique class.TestModule8.uint64: ClassName;

// Constructor function declaration
function #TestModule8.G.GUint64() : DatatypeType;

const unique ##TestModule8.G.GUint64: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#TestModule8.G.GUint64()) == ##TestModule8.G.GUint64;

function TestModule8.G.GUint64_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GUint64_q(d) } 
  TestModule8.G.GUint64_q(d) <==> DatatypeCtorId(d) == ##TestModule8.G.GUint64);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GUint64_q(d) } 
  TestModule8.G.GUint64_q(d) ==> d == #TestModule8.G.GUint64());

function Tclass.TestModule8.G() : Ty;

const unique Tagclass.TestModule8.G: TyTag;

// Tclass.TestModule8.G Tag
axiom Tag(Tclass.TestModule8.G()) == Tagclass.TestModule8.G
   && TagFamily(Tclass.TestModule8.G()) == tytagFamily$G;

// Box/unbox axiom for Tclass.TestModule8.G
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TestModule8.G()) } 
  $IsBox(bx, Tclass.TestModule8.G())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.TestModule8.G()));

// Constructor $Is
axiom $Is(#TestModule8.G.GUint64(), Tclass.TestModule8.G());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#TestModule8.G.GUint64(), Tclass.TestModule8.G(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#TestModule8.G.GUint64(), Tclass.TestModule8.G(), $h));

// Constructor literal
axiom #TestModule8.G.GUint64() == Lit(#TestModule8.G.GUint64());

// Constructor function declaration
function #TestModule8.G.GArray(DatatypeType) : DatatypeType;

const unique ##TestModule8.G.GArray: DtCtorId;

// Constructor identifier
axiom (forall a#5#0#0: DatatypeType :: 
  { #TestModule8.G.GArray(a#5#0#0) } 
  DatatypeCtorId(#TestModule8.G.GArray(a#5#0#0)) == ##TestModule8.G.GArray);

function TestModule8.G.GArray_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GArray_q(d) } 
  TestModule8.G.GArray_q(d) <==> DatatypeCtorId(d) == ##TestModule8.G.GArray);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GArray_q(d) } 
  TestModule8.G.GArray_q(d)
     ==> (exists a#6#0#0: DatatypeType :: d == #TestModule8.G.GArray(a#6#0#0)));

// Constructor $Is
axiom (forall a#7#0#0: DatatypeType :: 
  { $Is(#TestModule8.G.GArray(a#7#0#0), Tclass.TestModule8.G()) } 
  $Is(#TestModule8.G.GArray(a#7#0#0), Tclass.TestModule8.G())
     <==> $Is(a#7#0#0, Tclass.TestModule8.G()));

// Constructor $IsAlloc
axiom (forall a#8#0#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#TestModule8.G.GArray(a#8#0#0), Tclass.TestModule8.G(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TestModule8.G.GArray(a#8#0#0), Tclass.TestModule8.G(), $h)
       <==> $IsAlloc(a#8#0#0, Tclass.TestModule8.G(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(TestModule8.G.elt(d), Tclass.TestModule8.G(), $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.G.GArray_q(d)
       && $IsAlloc(d, Tclass.TestModule8.G(), $h)
     ==> $IsAlloc(TestModule8.G.elt(d), Tclass.TestModule8.G(), $h));

// Constructor literal
axiom (forall a#9#0#0: DatatypeType :: 
  { #TestModule8.G.GArray(Lit(a#9#0#0)) } 
  #TestModule8.G.GArray(Lit(a#9#0#0)) == Lit(#TestModule8.G.GArray(a#9#0#0)));

function TestModule8.G.elt(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#10#0#0: DatatypeType :: 
  { #TestModule8.G.GArray(a#10#0#0) } 
  TestModule8.G.elt(#TestModule8.G.GArray(a#10#0#0)) == a#10#0#0);

// Inductive rank
axiom (forall a#11#0#0: DatatypeType :: 
  { #TestModule8.G.GArray(a#11#0#0) } 
  DtRank(a#11#0#0) < DtRank(#TestModule8.G.GArray(a#11#0#0)));

// Constructor function declaration
function #TestModule8.G.GTuple(Seq Box) : DatatypeType;

const unique ##TestModule8.G.GTuple: DtCtorId;

// Constructor identifier
axiom (forall a#12#0#0: Seq Box :: 
  { #TestModule8.G.GTuple(a#12#0#0) } 
  DatatypeCtorId(#TestModule8.G.GTuple(a#12#0#0)) == ##TestModule8.G.GTuple);

function TestModule8.G.GTuple_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GTuple_q(d) } 
  TestModule8.G.GTuple_q(d) <==> DatatypeCtorId(d) == ##TestModule8.G.GTuple);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GTuple_q(d) } 
  TestModule8.G.GTuple_q(d)
     ==> (exists a#13#0#0: Seq Box :: d == #TestModule8.G.GTuple(a#13#0#0)));

// Constructor $Is
axiom (forall a#14#0#0: Seq Box :: 
  { $Is(#TestModule8.G.GTuple(a#14#0#0), Tclass.TestModule8.G()) } 
  $Is(#TestModule8.G.GTuple(a#14#0#0), Tclass.TestModule8.G())
     <==> $Is(a#14#0#0, TSeq(Tclass.TestModule8.G())));

// Constructor $IsAlloc
axiom (forall a#15#0#0: Seq Box, $h: Heap :: 
  { $IsAlloc(#TestModule8.G.GTuple(a#15#0#0), Tclass.TestModule8.G(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TestModule8.G.GTuple(a#15#0#0), Tclass.TestModule8.G(), $h)
       <==> $IsAlloc(a#15#0#0, TSeq(Tclass.TestModule8.G()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(TestModule8.G.t(d), TSeq(Tclass.TestModule8.G()), $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.G.GTuple_q(d)
       && $IsAlloc(d, Tclass.TestModule8.G(), $h)
     ==> $IsAlloc(TestModule8.G.t(d), TSeq(Tclass.TestModule8.G()), $h));

// Constructor literal
axiom (forall a#16#0#0: Seq Box :: 
  { #TestModule8.G.GTuple(Lit(a#16#0#0)) } 
  #TestModule8.G.GTuple(Lit(a#16#0#0)) == Lit(#TestModule8.G.GTuple(a#16#0#0)));

function TestModule8.G.t(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#17#0#0: Seq Box :: 
  { #TestModule8.G.GTuple(a#17#0#0) } 
  TestModule8.G.t(#TestModule8.G.GTuple(a#17#0#0)) == a#17#0#0);

// Inductive seq element rank
axiom (forall a#18#0#0: Seq Box, i: int :: 
  { Seq#Index(a#18#0#0, i), #TestModule8.G.GTuple(a#18#0#0) } 
  0 <= i && i < Seq#Length(a#18#0#0)
     ==> DtRank($Unbox(Seq#Index(a#18#0#0, i)): DatatypeType)
       < DtRank(#TestModule8.G.GTuple(a#18#0#0)));

// Inductive seq rank
axiom (forall a#19#0#0: Seq Box :: 
  { #TestModule8.G.GTuple(a#19#0#0) } 
  Seq#Rank(a#19#0#0) < DtRank(#TestModule8.G.GTuple(a#19#0#0)));

// Constructor function declaration
function #TestModule8.G.GByteArray() : DatatypeType;

const unique ##TestModule8.G.GByteArray: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#TestModule8.G.GByteArray()) == ##TestModule8.G.GByteArray;

function TestModule8.G.GByteArray_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GByteArray_q(d) } 
  TestModule8.G.GByteArray_q(d)
     <==> DatatypeCtorId(d) == ##TestModule8.G.GByteArray);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GByteArray_q(d) } 
  TestModule8.G.GByteArray_q(d) ==> d == #TestModule8.G.GByteArray());

// Constructor $Is
axiom $Is(#TestModule8.G.GByteArray(), Tclass.TestModule8.G());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#TestModule8.G.GByteArray(), Tclass.TestModule8.G(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#TestModule8.G.GByteArray(), Tclass.TestModule8.G(), $h));

// Constructor literal
axiom #TestModule8.G.GByteArray() == Lit(#TestModule8.G.GByteArray());

// Constructor function declaration
function #TestModule8.G.GTaggedUnion(Seq Box) : DatatypeType;

const unique ##TestModule8.G.GTaggedUnion: DtCtorId;

// Constructor identifier
axiom (forall a#25#0#0: Seq Box :: 
  { #TestModule8.G.GTaggedUnion(a#25#0#0) } 
  DatatypeCtorId(#TestModule8.G.GTaggedUnion(a#25#0#0))
     == ##TestModule8.G.GTaggedUnion);

function TestModule8.G.GTaggedUnion_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GTaggedUnion_q(d) } 
  TestModule8.G.GTaggedUnion_q(d)
     <==> DatatypeCtorId(d) == ##TestModule8.G.GTaggedUnion);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GTaggedUnion_q(d) } 
  TestModule8.G.GTaggedUnion_q(d)
     ==> (exists a#26#0#0: Seq Box :: d == #TestModule8.G.GTaggedUnion(a#26#0#0)));

// Constructor $Is
axiom (forall a#27#0#0: Seq Box :: 
  { $Is(#TestModule8.G.GTaggedUnion(a#27#0#0), Tclass.TestModule8.G()) } 
  $Is(#TestModule8.G.GTaggedUnion(a#27#0#0), Tclass.TestModule8.G())
     <==> $Is(a#27#0#0, TSeq(Tclass.TestModule8.G())));

// Constructor $IsAlloc
axiom (forall a#28#0#0: Seq Box, $h: Heap :: 
  { $IsAlloc(#TestModule8.G.GTaggedUnion(a#28#0#0), Tclass.TestModule8.G(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TestModule8.G.GTaggedUnion(a#28#0#0), Tclass.TestModule8.G(), $h)
       <==> $IsAlloc(a#28#0#0, TSeq(Tclass.TestModule8.G()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(TestModule8.G.cases(d), TSeq(Tclass.TestModule8.G()), $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.G.GTaggedUnion_q(d)
       && $IsAlloc(d, Tclass.TestModule8.G(), $h)
     ==> $IsAlloc(TestModule8.G.cases(d), TSeq(Tclass.TestModule8.G()), $h));

// Constructor literal
axiom (forall a#29#0#0: Seq Box :: 
  { #TestModule8.G.GTaggedUnion(Lit(a#29#0#0)) } 
  #TestModule8.G.GTaggedUnion(Lit(a#29#0#0))
     == Lit(#TestModule8.G.GTaggedUnion(a#29#0#0)));

function TestModule8.G.cases(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#30#0#0: Seq Box :: 
  { #TestModule8.G.GTaggedUnion(a#30#0#0) } 
  TestModule8.G.cases(#TestModule8.G.GTaggedUnion(a#30#0#0)) == a#30#0#0);

// Inductive seq element rank
axiom (forall a#31#0#0: Seq Box, i: int :: 
  { Seq#Index(a#31#0#0, i), #TestModule8.G.GTaggedUnion(a#31#0#0) } 
  0 <= i && i < Seq#Length(a#31#0#0)
     ==> DtRank($Unbox(Seq#Index(a#31#0#0, i)): DatatypeType)
       < DtRank(#TestModule8.G.GTaggedUnion(a#31#0#0)));

// Inductive seq rank
axiom (forall a#32#0#0: Seq Box :: 
  { #TestModule8.G.GTaggedUnion(a#32#0#0) } 
  Seq#Rank(a#32#0#0) < DtRank(#TestModule8.G.GTaggedUnion(a#32#0#0)));

// Depth-one case-split function
function $IsA#TestModule8.G(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#TestModule8.G(d) } 
  $IsA#TestModule8.G(d)
     ==> TestModule8.G.GUint64_q(d)
       || TestModule8.G.GArray_q(d)
       || TestModule8.G.GTuple_q(d)
       || TestModule8.G.GByteArray_q(d)
       || TestModule8.G.GTaggedUnion_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { TestModule8.G.GTaggedUnion_q(d), $Is(d, Tclass.TestModule8.G()) } 
    { TestModule8.G.GByteArray_q(d), $Is(d, Tclass.TestModule8.G()) } 
    { TestModule8.G.GTuple_q(d), $Is(d, Tclass.TestModule8.G()) } 
    { TestModule8.G.GArray_q(d), $Is(d, Tclass.TestModule8.G()) } 
    { TestModule8.G.GUint64_q(d), $Is(d, Tclass.TestModule8.G()) } 
  $Is(d, Tclass.TestModule8.G())
     ==> TestModule8.G.GUint64_q(d)
       || TestModule8.G.GArray_q(d)
       || TestModule8.G.GTuple_q(d)
       || TestModule8.G.GByteArray_q(d)
       || TestModule8.G.GTaggedUnion_q(d));

// Datatype extensional equality declaration
function TestModule8.G#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #TestModule8.G.GUint64
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.G#Equal(a, b), TestModule8.G.GUint64_q(a) } 
    { TestModule8.G#Equal(a, b), TestModule8.G.GUint64_q(b) } 
  TestModule8.G.GUint64_q(a) && TestModule8.G.GUint64_q(b)
     ==> (TestModule8.G#Equal(a, b) <==> true));

// Datatype extensional equality definition: #TestModule8.G.GArray
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.G#Equal(a, b), TestModule8.G.GArray_q(a) } 
    { TestModule8.G#Equal(a, b), TestModule8.G.GArray_q(b) } 
  TestModule8.G.GArray_q(a) && TestModule8.G.GArray_q(b)
     ==> (TestModule8.G#Equal(a, b)
       <==> TestModule8.G#Equal(TestModule8.G.elt(a), TestModule8.G.elt(b))));

// Datatype extensional equality definition: #TestModule8.G.GTuple
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.G#Equal(a, b), TestModule8.G.GTuple_q(a) } 
    { TestModule8.G#Equal(a, b), TestModule8.G.GTuple_q(b) } 
  TestModule8.G.GTuple_q(a) && TestModule8.G.GTuple_q(b)
     ==> (TestModule8.G#Equal(a, b)
       <==> Seq#Equal(TestModule8.G.t(a), TestModule8.G.t(b))));

// Datatype extensional equality definition: #TestModule8.G.GByteArray
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.G#Equal(a, b), TestModule8.G.GByteArray_q(a) } 
    { TestModule8.G#Equal(a, b), TestModule8.G.GByteArray_q(b) } 
  TestModule8.G.GByteArray_q(a) && TestModule8.G.GByteArray_q(b)
     ==> (TestModule8.G#Equal(a, b) <==> true));

// Datatype extensional equality definition: #TestModule8.G.GTaggedUnion
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.G#Equal(a, b), TestModule8.G.GTaggedUnion_q(a) } 
    { TestModule8.G#Equal(a, b), TestModule8.G.GTaggedUnion_q(b) } 
  TestModule8.G.GTaggedUnion_q(a) && TestModule8.G.GTaggedUnion_q(b)
     ==> (TestModule8.G#Equal(a, b)
       <==> Seq#Equal(TestModule8.G.cases(a), TestModule8.G.cases(b))));

// Datatype extensionality axiom: TestModule8.G
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.G#Equal(a, b) } 
  TestModule8.G#Equal(a, b) <==> a == b);

const unique class.TestModule8.G: ClassName;

// Constructor function declaration
function #TestModule8.V.VUint64(int) : DatatypeType;

const unique ##TestModule8.V.VUint64: DtCtorId;

// Constructor identifier
axiom (forall a#33#0#0: int :: 
  { #TestModule8.V.VUint64(a#33#0#0) } 
  DatatypeCtorId(#TestModule8.V.VUint64(a#33#0#0)) == ##TestModule8.V.VUint64);

function TestModule8.V.VUint64_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.V.VUint64_q(d) } 
  TestModule8.V.VUint64_q(d) <==> DatatypeCtorId(d) == ##TestModule8.V.VUint64);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.V.VUint64_q(d) } 
  TestModule8.V.VUint64_q(d)
     ==> (exists a#34#0#0: int :: d == #TestModule8.V.VUint64(a#34#0#0)));

function Tclass.TestModule8.V() : Ty;

const unique Tagclass.TestModule8.V: TyTag;

// Tclass.TestModule8.V Tag
axiom Tag(Tclass.TestModule8.V()) == Tagclass.TestModule8.V
   && TagFamily(Tclass.TestModule8.V()) == tytagFamily$V;

// Box/unbox axiom for Tclass.TestModule8.V
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TestModule8.V()) } 
  $IsBox(bx, Tclass.TestModule8.V())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.TestModule8.V()));

// Constructor $Is
axiom (forall a#35#0#0: int :: 
  { $Is(#TestModule8.V.VUint64(a#35#0#0), Tclass.TestModule8.V()) } 
  $Is(#TestModule8.V.VUint64(a#35#0#0), Tclass.TestModule8.V())
     <==> $Is(a#35#0#0, Tclass.TestModule8.uint64()));

// Constructor $IsAlloc
axiom (forall a#36#0#0: int, $h: Heap :: 
  { $IsAlloc(#TestModule8.V.VUint64(a#36#0#0), Tclass.TestModule8.V(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TestModule8.V.VUint64(a#36#0#0), Tclass.TestModule8.V(), $h)
       <==> $IsAlloc(a#36#0#0, Tclass.TestModule8.uint64(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(TestModule8.V.u(d), Tclass.TestModule8.uint64(), $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.V.VUint64_q(d)
       && $IsAlloc(d, Tclass.TestModule8.V(), $h)
     ==> $IsAlloc(TestModule8.V.u(d), Tclass.TestModule8.uint64(), $h));

// Constructor literal
axiom (forall a#37#0#0: int :: 
  { #TestModule8.V.VUint64(LitInt(a#37#0#0)) } 
  #TestModule8.V.VUint64(LitInt(a#37#0#0))
     == Lit(#TestModule8.V.VUint64(a#37#0#0)));

function TestModule8.V.u(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#38#0#0: int :: 
  { #TestModule8.V.VUint64(a#38#0#0) } 
  TestModule8.V.u(#TestModule8.V.VUint64(a#38#0#0)) == a#38#0#0);

// Constructor function declaration
function #TestModule8.V.VTuple(Seq Box) : DatatypeType;

const unique ##TestModule8.V.VTuple: DtCtorId;

// Constructor identifier
axiom (forall a#39#0#0: Seq Box :: 
  { #TestModule8.V.VTuple(a#39#0#0) } 
  DatatypeCtorId(#TestModule8.V.VTuple(a#39#0#0)) == ##TestModule8.V.VTuple);

function TestModule8.V.VTuple_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.V.VTuple_q(d) } 
  TestModule8.V.VTuple_q(d) <==> DatatypeCtorId(d) == ##TestModule8.V.VTuple);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.V.VTuple_q(d) } 
  TestModule8.V.VTuple_q(d)
     ==> (exists a#40#0#0: Seq Box :: d == #TestModule8.V.VTuple(a#40#0#0)));

// Constructor $Is
axiom (forall a#41#0#0: Seq Box :: 
  { $Is(#TestModule8.V.VTuple(a#41#0#0), Tclass.TestModule8.V()) } 
  $Is(#TestModule8.V.VTuple(a#41#0#0), Tclass.TestModule8.V())
     <==> $Is(a#41#0#0, TSeq(Tclass.TestModule8.V())));

// Constructor $IsAlloc
axiom (forall a#42#0#0: Seq Box, $h: Heap :: 
  { $IsAlloc(#TestModule8.V.VTuple(a#42#0#0), Tclass.TestModule8.V(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TestModule8.V.VTuple(a#42#0#0), Tclass.TestModule8.V(), $h)
       <==> $IsAlloc(a#42#0#0, TSeq(Tclass.TestModule8.V()), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(TestModule8.V.t(d), TSeq(Tclass.TestModule8.V()), $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.V.VTuple_q(d)
       && $IsAlloc(d, Tclass.TestModule8.V(), $h)
     ==> $IsAlloc(TestModule8.V.t(d), TSeq(Tclass.TestModule8.V()), $h));

// Constructor literal
axiom (forall a#43#0#0: Seq Box :: 
  { #TestModule8.V.VTuple(Lit(a#43#0#0)) } 
  #TestModule8.V.VTuple(Lit(a#43#0#0)) == Lit(#TestModule8.V.VTuple(a#43#0#0)));

function TestModule8.V.t(DatatypeType) : Seq Box;

// Constructor injectivity
axiom (forall a#44#0#0: Seq Box :: 
  { #TestModule8.V.VTuple(a#44#0#0) } 
  TestModule8.V.t(#TestModule8.V.VTuple(a#44#0#0)) == a#44#0#0);

// Inductive seq element rank
axiom (forall a#45#0#0: Seq Box, i: int :: 
  { Seq#Index(a#45#0#0, i), #TestModule8.V.VTuple(a#45#0#0) } 
  0 <= i && i < Seq#Length(a#45#0#0)
     ==> DtRank($Unbox(Seq#Index(a#45#0#0, i)): DatatypeType)
       < DtRank(#TestModule8.V.VTuple(a#45#0#0)));

// Inductive seq rank
axiom (forall a#46#0#0: Seq Box :: 
  { #TestModule8.V.VTuple(a#46#0#0) } 
  Seq#Rank(a#46#0#0) < DtRank(#TestModule8.V.VTuple(a#46#0#0)));

// Constructor function declaration
function #TestModule8.V.VCase(int, DatatypeType) : DatatypeType;

const unique ##TestModule8.V.VCase: DtCtorId;

// Constructor identifier
axiom (forall a#47#0#0: int, a#47#1#0: DatatypeType :: 
  { #TestModule8.V.VCase(a#47#0#0, a#47#1#0) } 
  DatatypeCtorId(#TestModule8.V.VCase(a#47#0#0, a#47#1#0))
     == ##TestModule8.V.VCase);

function TestModule8.V.VCase_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.V.VCase_q(d) } 
  TestModule8.V.VCase_q(d) <==> DatatypeCtorId(d) == ##TestModule8.V.VCase);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.V.VCase_q(d) } 
  TestModule8.V.VCase_q(d)
     ==> (exists a#48#0#0: int, a#48#1#0: DatatypeType :: 
      d == #TestModule8.V.VCase(a#48#0#0, a#48#1#0)));

// Constructor $Is
axiom (forall a#49#0#0: int, a#49#1#0: DatatypeType :: 
  { $Is(#TestModule8.V.VCase(a#49#0#0, a#49#1#0), Tclass.TestModule8.V()) } 
  $Is(#TestModule8.V.VCase(a#49#0#0, a#49#1#0), Tclass.TestModule8.V())
     <==> $Is(a#49#0#0, Tclass.TestModule8.uint64())
       && $Is(a#49#1#0, Tclass.TestModule8.V()));

// Constructor $IsAlloc
axiom (forall a#50#0#0: int, a#50#1#0: DatatypeType, $h: Heap :: 
  { $IsAlloc(#TestModule8.V.VCase(a#50#0#0, a#50#1#0), Tclass.TestModule8.V(), $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TestModule8.V.VCase(a#50#0#0, a#50#1#0), Tclass.TestModule8.V(), $h)
       <==> $IsAlloc(a#50#0#0, Tclass.TestModule8.uint64(), $h)
         && $IsAlloc(a#50#1#0, Tclass.TestModule8.V(), $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(TestModule8.V.c(d), Tclass.TestModule8.uint64(), $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.V.VCase_q(d)
       && $IsAlloc(d, Tclass.TestModule8.V(), $h)
     ==> $IsAlloc(TestModule8.V.c(d), Tclass.TestModule8.uint64(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(TestModule8.V.val(d), Tclass.TestModule8.V(), $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.V.VCase_q(d)
       && $IsAlloc(d, Tclass.TestModule8.V(), $h)
     ==> $IsAlloc(TestModule8.V.val(d), Tclass.TestModule8.V(), $h));

// Constructor literal
axiom (forall a#51#0#0: int, a#51#1#0: DatatypeType :: 
  { #TestModule8.V.VCase(LitInt(a#51#0#0), Lit(a#51#1#0)) } 
  #TestModule8.V.VCase(LitInt(a#51#0#0), Lit(a#51#1#0))
     == Lit(#TestModule8.V.VCase(a#51#0#0, a#51#1#0)));

function TestModule8.V.c(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#52#0#0: int, a#52#1#0: DatatypeType :: 
  { #TestModule8.V.VCase(a#52#0#0, a#52#1#0) } 
  TestModule8.V.c(#TestModule8.V.VCase(a#52#0#0, a#52#1#0)) == a#52#0#0);

function TestModule8.V.val(DatatypeType) : DatatypeType;

// Constructor injectivity
axiom (forall a#53#0#0: int, a#53#1#0: DatatypeType :: 
  { #TestModule8.V.VCase(a#53#0#0, a#53#1#0) } 
  TestModule8.V.val(#TestModule8.V.VCase(a#53#0#0, a#53#1#0)) == a#53#1#0);

// Inductive rank
axiom (forall a#54#0#0: int, a#54#1#0: DatatypeType :: 
  { #TestModule8.V.VCase(a#54#0#0, a#54#1#0) } 
  DtRank(a#54#1#0) < DtRank(#TestModule8.V.VCase(a#54#0#0, a#54#1#0)));

// Depth-one case-split function
function $IsA#TestModule8.V(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#TestModule8.V(d) } 
  $IsA#TestModule8.V(d)
     ==> TestModule8.V.VUint64_q(d)
       || TestModule8.V.VTuple_q(d)
       || TestModule8.V.VCase_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { TestModule8.V.VCase_q(d), $Is(d, Tclass.TestModule8.V()) } 
    { TestModule8.V.VTuple_q(d), $Is(d, Tclass.TestModule8.V()) } 
    { TestModule8.V.VUint64_q(d), $Is(d, Tclass.TestModule8.V()) } 
  $Is(d, Tclass.TestModule8.V())
     ==> TestModule8.V.VUint64_q(d)
       || TestModule8.V.VTuple_q(d)
       || TestModule8.V.VCase_q(d));

// Datatype extensional equality declaration
function TestModule8.V#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #TestModule8.V.VUint64
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.V#Equal(a, b), TestModule8.V.VUint64_q(a) } 
    { TestModule8.V#Equal(a, b), TestModule8.V.VUint64_q(b) } 
  TestModule8.V.VUint64_q(a) && TestModule8.V.VUint64_q(b)
     ==> (TestModule8.V#Equal(a, b) <==> TestModule8.V.u(a) == TestModule8.V.u(b)));

// Datatype extensional equality definition: #TestModule8.V.VTuple
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.V#Equal(a, b), TestModule8.V.VTuple_q(a) } 
    { TestModule8.V#Equal(a, b), TestModule8.V.VTuple_q(b) } 
  TestModule8.V.VTuple_q(a) && TestModule8.V.VTuple_q(b)
     ==> (TestModule8.V#Equal(a, b)
       <==> Seq#Equal(TestModule8.V.t(a), TestModule8.V.t(b))));

// Datatype extensional equality definition: #TestModule8.V.VCase
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.V#Equal(a, b), TestModule8.V.VCase_q(a) } 
    { TestModule8.V#Equal(a, b), TestModule8.V.VCase_q(b) } 
  TestModule8.V.VCase_q(a) && TestModule8.V.VCase_q(b)
     ==> (TestModule8.V#Equal(a, b)
       <==> TestModule8.V.c(a) == TestModule8.V.c(b)
         && TestModule8.V#Equal(TestModule8.V.val(a), TestModule8.V.val(b))));

// Datatype extensionality axiom: TestModule8.V
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.V#Equal(a, b) } 
  TestModule8.V#Equal(a, b) <==> a == b);

const unique class.TestModule8.V: ClassName;

// Constructor function declaration
function #TestModule8.CRequest.CRequest(Box, int, Box) : DatatypeType;

const unique ##TestModule8.CRequest.CRequest: DtCtorId;

// Constructor identifier
axiom (forall a#55#0#0: Box, a#55#1#0: int, a#55#2#0: Box :: 
  { #TestModule8.CRequest.CRequest(a#55#0#0, a#55#1#0, a#55#2#0) } 
  DatatypeCtorId(#TestModule8.CRequest.CRequest(a#55#0#0, a#55#1#0, a#55#2#0))
     == ##TestModule8.CRequest.CRequest);

function TestModule8.CRequest.CRequest_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.CRequest.CRequest_q(d) } 
  TestModule8.CRequest.CRequest_q(d)
     <==> DatatypeCtorId(d) == ##TestModule8.CRequest.CRequest);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.CRequest.CRequest_q(d) } 
  TestModule8.CRequest.CRequest_q(d)
     ==> (exists a#56#0#0: Box, a#56#1#0: int, a#56#2#0: Box :: 
      d == #TestModule8.CRequest.CRequest(a#56#0#0, a#56#1#0, a#56#2#0)));

function Tclass.TestModule8.CRequest() : Ty;

const unique Tagclass.TestModule8.CRequest: TyTag;

// Tclass.TestModule8.CRequest Tag
axiom Tag(Tclass.TestModule8.CRequest()) == Tagclass.TestModule8.CRequest
   && TagFamily(Tclass.TestModule8.CRequest()) == tytagFamily$CRequest;

// Box/unbox axiom for Tclass.TestModule8.CRequest
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TestModule8.CRequest()) } 
  $IsBox(bx, Tclass.TestModule8.CRequest())
     ==> $Box($Unbox(bx): DatatypeType) == bx
       && $Is($Unbox(bx): DatatypeType, Tclass.TestModule8.CRequest()));

// Constructor $Is
axiom (forall a#57#0#0: Box, a#57#1#0: int, a#57#2#0: Box :: 
  { $Is(#TestModule8.CRequest.CRequest(a#57#0#0, a#57#1#0, a#57#2#0), 
      Tclass.TestModule8.CRequest()) } 
  $Is(#TestModule8.CRequest.CRequest(a#57#0#0, a#57#1#0, a#57#2#0), 
      Tclass.TestModule8.CRequest())
     <==> $IsBox(a#57#0#0, #$EndPoint)
       && $Is(a#57#1#0, Tclass.TestModule8.uint64())
       && $IsBox(a#57#2#0, #$CAppMessage));

// Constructor $IsAlloc
axiom (forall a#58#0#0: Box, a#58#1#0: int, a#58#2#0: Box, $h: Heap :: 
  { $IsAlloc(#TestModule8.CRequest.CRequest(a#58#0#0, a#58#1#0, a#58#2#0), 
      Tclass.TestModule8.CRequest(), 
      $h) } 
  $IsGoodHeap($h)
     ==> ($IsAlloc(#TestModule8.CRequest.CRequest(a#58#0#0, a#58#1#0, a#58#2#0), 
        Tclass.TestModule8.CRequest(), 
        $h)
       <==> $IsAllocBox(a#58#0#0, #$EndPoint, $h)
         && $IsAlloc(a#58#1#0, Tclass.TestModule8.uint64(), $h)
         && $IsAllocBox(a#58#2#0, #$CAppMessage, $h)));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAllocBox(TestModule8.CRequest.client(d), #$EndPoint, $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.CRequest.CRequest_q(d)
       && $IsAlloc(d, Tclass.TestModule8.CRequest(), $h)
     ==> $IsAllocBox(TestModule8.CRequest.client(d), #$EndPoint, $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAlloc(TestModule8.CRequest.seqno(d), Tclass.TestModule8.uint64(), $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.CRequest.CRequest_q(d)
       && $IsAlloc(d, Tclass.TestModule8.CRequest(), $h)
     ==> $IsAlloc(TestModule8.CRequest.seqno(d), Tclass.TestModule8.uint64(), $h));

// Destructor $IsAlloc
axiom (forall d: DatatypeType, $h: Heap :: 
  { $IsAllocBox(TestModule8.CRequest.request(d), #$CAppMessage, $h) } 
  $IsGoodHeap($h)
       && 
      TestModule8.CRequest.CRequest_q(d)
       && $IsAlloc(d, Tclass.TestModule8.CRequest(), $h)
     ==> $IsAllocBox(TestModule8.CRequest.request(d), #$CAppMessage, $h));

// Constructor literal
axiom (forall a#59#0#0: Box, a#59#1#0: int, a#59#2#0: Box :: 
  { #TestModule8.CRequest.CRequest(Lit(a#59#0#0), LitInt(a#59#1#0), Lit(a#59#2#0)) } 
  #TestModule8.CRequest.CRequest(Lit(a#59#0#0), LitInt(a#59#1#0), Lit(a#59#2#0))
     == Lit(#TestModule8.CRequest.CRequest(a#59#0#0, a#59#1#0, a#59#2#0)));

function TestModule8.CRequest.client(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#60#0#0: Box, a#60#1#0: int, a#60#2#0: Box :: 
  { #TestModule8.CRequest.CRequest(a#60#0#0, a#60#1#0, a#60#2#0) } 
  TestModule8.CRequest.client(#TestModule8.CRequest.CRequest(a#60#0#0, a#60#1#0, a#60#2#0))
     == a#60#0#0);

// Inductive rank
axiom (forall a#61#0#0: Box, a#61#1#0: int, a#61#2#0: Box :: 
  { #TestModule8.CRequest.CRequest(a#61#0#0, a#61#1#0, a#61#2#0) } 
  BoxRank(a#61#0#0)
     < DtRank(#TestModule8.CRequest.CRequest(a#61#0#0, a#61#1#0, a#61#2#0)));

function TestModule8.CRequest.seqno(DatatypeType) : int;

// Constructor injectivity
axiom (forall a#62#0#0: Box, a#62#1#0: int, a#62#2#0: Box :: 
  { #TestModule8.CRequest.CRequest(a#62#0#0, a#62#1#0, a#62#2#0) } 
  TestModule8.CRequest.seqno(#TestModule8.CRequest.CRequest(a#62#0#0, a#62#1#0, a#62#2#0))
     == a#62#1#0);

function TestModule8.CRequest.request(DatatypeType) : Box;

// Constructor injectivity
axiom (forall a#63#0#0: Box, a#63#1#0: int, a#63#2#0: Box :: 
  { #TestModule8.CRequest.CRequest(a#63#0#0, a#63#1#0, a#63#2#0) } 
  TestModule8.CRequest.request(#TestModule8.CRequest.CRequest(a#63#0#0, a#63#1#0, a#63#2#0))
     == a#63#2#0);

// Inductive rank
axiom (forall a#64#0#0: Box, a#64#1#0: int, a#64#2#0: Box :: 
  { #TestModule8.CRequest.CRequest(a#64#0#0, a#64#1#0, a#64#2#0) } 
  BoxRank(a#64#2#0)
     < DtRank(#TestModule8.CRequest.CRequest(a#64#0#0, a#64#1#0, a#64#2#0)));

// Constructor function declaration
function #TestModule8.CRequest.CRequestNoOp() : DatatypeType;

const unique ##TestModule8.CRequest.CRequestNoOp: DtCtorId;

// Constructor identifier
axiom DatatypeCtorId(#TestModule8.CRequest.CRequestNoOp())
   == ##TestModule8.CRequest.CRequestNoOp;

function TestModule8.CRequest.CRequestNoOp_q(DatatypeType) : bool;

// Questionmark and identifier
axiom (forall d: DatatypeType :: 
  { TestModule8.CRequest.CRequestNoOp_q(d) } 
  TestModule8.CRequest.CRequestNoOp_q(d)
     <==> DatatypeCtorId(d) == ##TestModule8.CRequest.CRequestNoOp);

// Constructor questionmark has arguments
axiom (forall d: DatatypeType :: 
  { TestModule8.CRequest.CRequestNoOp_q(d) } 
  TestModule8.CRequest.CRequestNoOp_q(d)
     ==> d == #TestModule8.CRequest.CRequestNoOp());

// Constructor $Is
axiom $Is(#TestModule8.CRequest.CRequestNoOp(), Tclass.TestModule8.CRequest());

// Constructor $IsAlloc
axiom (forall $h: Heap :: 
  { $IsAlloc(#TestModule8.CRequest.CRequestNoOp(), Tclass.TestModule8.CRequest(), $h) } 
  $IsGoodHeap($h)
     ==> $IsAlloc(#TestModule8.CRequest.CRequestNoOp(), Tclass.TestModule8.CRequest(), $h));

// Constructor literal
axiom #TestModule8.CRequest.CRequestNoOp()
   == Lit(#TestModule8.CRequest.CRequestNoOp());

// Depth-one case-split function
function $IsA#TestModule8.CRequest(DatatypeType) : bool;

// Depth-one case-split axiom
axiom (forall d: DatatypeType :: 
  { $IsA#TestModule8.CRequest(d) } 
  $IsA#TestModule8.CRequest(d)
     ==> TestModule8.CRequest.CRequest_q(d) || TestModule8.CRequest.CRequestNoOp_q(d));

// Questionmark data type disjunctivity
axiom (forall d: DatatypeType :: 
  { TestModule8.CRequest.CRequestNoOp_q(d), $Is(d, Tclass.TestModule8.CRequest()) } 
    { TestModule8.CRequest.CRequest_q(d), $Is(d, Tclass.TestModule8.CRequest()) } 
  $Is(d, Tclass.TestModule8.CRequest())
     ==> TestModule8.CRequest.CRequest_q(d) || TestModule8.CRequest.CRequestNoOp_q(d));

// Datatype extensional equality declaration
function TestModule8.CRequest#Equal(DatatypeType, DatatypeType) : bool;

// Datatype extensional equality definition: #TestModule8.CRequest.CRequest
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.CRequest#Equal(a, b), TestModule8.CRequest.CRequest_q(a) } 
    { TestModule8.CRequest#Equal(a, b), TestModule8.CRequest.CRequest_q(b) } 
  TestModule8.CRequest.CRequest_q(a) && TestModule8.CRequest.CRequest_q(b)
     ==> (TestModule8.CRequest#Equal(a, b)
       <==> TestModule8.CRequest.client(a) == TestModule8.CRequest.client(b)
         && TestModule8.CRequest.seqno(a) == TestModule8.CRequest.seqno(b)
         && TestModule8.CRequest.request(a) == TestModule8.CRequest.request(b)));

// Datatype extensional equality definition: #TestModule8.CRequest.CRequestNoOp
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.CRequest#Equal(a, b), TestModule8.CRequest.CRequestNoOp_q(a) } 
    { TestModule8.CRequest#Equal(a, b), TestModule8.CRequest.CRequestNoOp_q(b) } 
  TestModule8.CRequest.CRequestNoOp_q(a) && TestModule8.CRequest.CRequestNoOp_q(b)
     ==> (TestModule8.CRequest#Equal(a, b) <==> true));

// Datatype extensionality axiom: TestModule8.CRequest
axiom (forall a: DatatypeType, b: DatatypeType :: 
  { TestModule8.CRequest#Equal(a, b) } 
  TestModule8.CRequest#Equal(a, b) <==> a == b);

const unique class.TestModule8.CRequest: ClassName;

const #$EndPoint: Ty;

const unique class.TestModule8.EndPoint: ClassName;

const #$CAppMessage: Ty;

const unique class.TestModule8.CAppMessage: ClassName;

const unique class.TestModule8.__default: ClassName;

function Tclass.TestModule8.__default() : Ty;

const unique Tagclass.TestModule8.__default: TyTag;

// Tclass.TestModule8.__default Tag
axiom Tag(Tclass.TestModule8.__default()) == Tagclass.TestModule8.__default
   && TagFamily(Tclass.TestModule8.__default()) == tytagFamily$_default;

// Box/unbox axiom for Tclass.TestModule8.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass.TestModule8.__default()) } 
  $IsBox(bx, Tclass.TestModule8.__default())
     ==> $Box($Unbox(bx): ref) == bx
       && $Is($Unbox(bx): ref, Tclass.TestModule8.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass.TestModule8.__default()) } 
  $Is($o, Tclass.TestModule8.__default())
     <==> $o == null || dtype($o) == Tclass.TestModule8.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass.TestModule8.__default(), $h) } 
  $IsAlloc($o, Tclass.TestModule8.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

// function declaration for TestModule8._default.ValInGrammar
function TestModule8.__default.ValInGrammar($ly: LayerType, val#0: DatatypeType, grammar#0: DatatypeType) : bool;

function TestModule8.__default.ValInGrammar#canCall(val#0: DatatypeType, grammar#0: DatatypeType) : bool;

// layer synonym axiom
axiom (forall $ly: LayerType, val#0: DatatypeType, grammar#0: DatatypeType :: 
  { TestModule8.__default.ValInGrammar($LS($ly), val#0, grammar#0) } 
  TestModule8.__default.ValInGrammar($LS($ly), val#0, grammar#0)
     == TestModule8.__default.ValInGrammar($ly, val#0, grammar#0));

// fuel synonym axiom
axiom (forall $ly: LayerType, val#0: DatatypeType, grammar#0: DatatypeType :: 
  { TestModule8.__default.ValInGrammar(AsFuelBottom($ly), val#0, grammar#0) } 
  TestModule8.__default.ValInGrammar($ly, val#0, grammar#0)
     == TestModule8.__default.ValInGrammar($LZ, val#0, grammar#0));

// consequence axiom for TestModule8.__default.ValInGrammar
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, val#0: DatatypeType, grammar#0: DatatypeType :: 
    { TestModule8.__default.ValInGrammar($ly, val#0, grammar#0) } 
    TestModule8.__default.ValInGrammar#canCall(val#0, grammar#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && $Is(grammar#0, Tclass.TestModule8.G()))
       ==> true);

function TestModule8.__default.ValInGrammar#requires(LayerType, DatatypeType, DatatypeType) : bool;

// #requires axiom for TestModule8.__default.ValInGrammar
axiom (forall $ly: LayerType, val#0: DatatypeType, grammar#0: DatatypeType :: 
  { TestModule8.__default.ValInGrammar#requires($ly, val#0, grammar#0) } 
  $Is(val#0, Tclass.TestModule8.V()) && $Is(grammar#0, Tclass.TestModule8.G())
     ==> TestModule8.__default.ValInGrammar#requires($ly, val#0, grammar#0) == true);

// definition axiom for TestModule8.__default.ValInGrammar (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, val#0: DatatypeType, grammar#0: DatatypeType :: 
    { TestModule8.__default.ValInGrammar($LS($ly), val#0, grammar#0) } 
    TestModule8.__default.ValInGrammar#canCall(val#0, grammar#0)
         || (4 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && $Is(grammar#0, Tclass.TestModule8.G()))
       ==> (!TestModule8.V.VUint64_q(val#0)
           ==> (TestModule8.V.VTuple_q(val#0)
               ==> (var t#1 := TestModule8.V.t(val#0); 
                TestModule8.G.GTuple_q(grammar#0)
                   ==> 
                  Seq#Length(t#1) == Seq#Length(TestModule8.G.t(grammar#0))
                   ==> (forall i#1: int :: 
                    { $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#1)): DatatypeType } 
                      { $Unbox(Seq#Index(t#1, i#1)): DatatypeType } 
                    LitInt(0) <= i#1
                       ==> 
                      i#1 < Seq#Length(t#1)
                       ==> TestModule8.__default.ValInGrammar#canCall($Unbox(Seq#Index(t#1, i#1)): DatatypeType, 
                        $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#1)): DatatypeType))))
             && (!TestModule8.V.VTuple_q(val#0)
               ==> (var val#2 := TestModule8.V.val(val#0); 
                (var c#1 := TestModule8.V.c(val#0); 
                  TestModule8.G.GTaggedUnion_q(grammar#0)
                     ==> 
                    c#1 < Seq#Length(TestModule8.G.cases(grammar#0))
                     ==> TestModule8.__default.ValInGrammar#canCall(val#2, $Unbox(Seq#Index(TestModule8.G.cases(grammar#0), c#1)): DatatypeType)))))
         && TestModule8.__default.ValInGrammar($LS($ly), val#0, grammar#0)
           == (if TestModule8.V.VUint64_q(val#0)
             then TestModule8.G.GUint64_q(grammar#0)
             else (if TestModule8.V.VTuple_q(val#0)
               then (var t#0 := TestModule8.V.t(val#0); 
                TestModule8.G.GTuple_q(grammar#0)
                   && Seq#Length(t#0) == Seq#Length(TestModule8.G.t(grammar#0))
                   && (forall i#0: int :: 
                    { $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#0)): DatatypeType } 
                      { $Unbox(Seq#Index(t#0, i#0)): DatatypeType } 
                    true
                       ==> 
                      LitInt(0) <= i#0 && i#0 < Seq#Length(t#0)
                       ==> TestModule8.__default.ValInGrammar($ly, 
                        $Unbox(Seq#Index(t#0, i#0)): DatatypeType, 
                        $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#0)): DatatypeType)))
               else (var val#1 := TestModule8.V.val(val#0); 
                (var c#0 := TestModule8.V.c(val#0); 
                  TestModule8.G.GTaggedUnion_q(grammar#0)
                     && c#0 < Seq#Length(TestModule8.G.cases(grammar#0))
                     && TestModule8.__default.ValInGrammar($ly, val#1, $Unbox(Seq#Index(TestModule8.G.cases(grammar#0), c#0)): DatatypeType))))));

// definition axiom for TestModule8.__default.ValInGrammar for all literals (revealed)
axiom 4 <= $FunctionContextHeight
   ==> (forall $ly: LayerType, val#0: DatatypeType, grammar#0: DatatypeType :: 
    {:weight 3} { TestModule8.__default.ValInGrammar($LS($ly), Lit(val#0), Lit(grammar#0)) } 
    TestModule8.__default.ValInGrammar#canCall(Lit(val#0), Lit(grammar#0))
         || (4 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && $Is(grammar#0, Tclass.TestModule8.G()))
       ==> (!Lit(TestModule8.V.VUint64_q(Lit(val#0)))
           ==> (Lit(TestModule8.V.VTuple_q(Lit(val#0)))
               ==> (var t#3 := Lit(TestModule8.V.t(Lit(val#0))); 
                Lit(TestModule8.G.GTuple_q(Lit(grammar#0)))
                   ==> 
                  Seq#Length(t#3) == Seq#Length(Lit(TestModule8.G.t(Lit(grammar#0))))
                   ==> (forall i#3: int :: 
                    { $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#3)): DatatypeType } 
                      { $Unbox(Seq#Index(t#3, i#3)): DatatypeType } 
                    LitInt(0) <= i#3
                       ==> 
                      i#3 < Seq#Length(t#3)
                       ==> TestModule8.__default.ValInGrammar#canCall($Unbox(Seq#Index(t#3, i#3)): DatatypeType, 
                        $Unbox(Seq#Index(Lit(TestModule8.G.t(Lit(grammar#0))), i#3)): DatatypeType))))
             && (!Lit(TestModule8.V.VTuple_q(Lit(val#0)))
               ==> (var val#4 := Lit(TestModule8.V.val(Lit(val#0))); 
                (var c#3 := LitInt(TestModule8.V.c(Lit(val#0))); 
                  Lit(TestModule8.G.GTaggedUnion_q(Lit(grammar#0)))
                     ==> 
                    c#3 < Seq#Length(Lit(TestModule8.G.cases(Lit(grammar#0))))
                     ==> TestModule8.__default.ValInGrammar#canCall(val#4, 
                      $Unbox(Seq#Index(Lit(TestModule8.G.cases(Lit(grammar#0))), c#3)): DatatypeType)))))
         && TestModule8.__default.ValInGrammar($LS($ly), Lit(val#0), Lit(grammar#0))
           == (if TestModule8.V.VUint64_q(Lit(val#0))
             then TestModule8.G.GUint64_q(Lit(grammar#0))
             else (if TestModule8.V.VTuple_q(Lit(val#0))
               then (var t#2 := Lit(TestModule8.V.t(Lit(val#0))); 
                TestModule8.G.GTuple_q(Lit(grammar#0))
                   && Seq#Length(t#2) == Seq#Length(Lit(TestModule8.G.t(Lit(grammar#0))))
                   && (forall i#2: int :: 
                    { $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#2)): DatatypeType } 
                      { $Unbox(Seq#Index(t#2, i#2)): DatatypeType } 
                    true
                       ==> 
                      LitInt(0) <= i#2 && i#2 < Seq#Length(t#2)
                       ==> TestModule8.__default.ValInGrammar($LS($ly), 
                        $Unbox(Seq#Index(t#2, i#2)): DatatypeType, 
                        $Unbox(Seq#Index(Lit(TestModule8.G.t(Lit(grammar#0))), i#2)): DatatypeType)))
               else (var val#3 := Lit(TestModule8.V.val(Lit(val#0))); 
                (var c#2 := LitInt(TestModule8.V.c(Lit(val#0))); 
                  TestModule8.G.GTaggedUnion_q(Lit(grammar#0))
                     && c#2 < Seq#Length(Lit(TestModule8.G.cases(Lit(grammar#0))))
                     && TestModule8.__default.ValInGrammar($LS($ly), 
                      val#3, 
                      $Unbox(Seq#Index(Lit(TestModule8.G.cases(Lit(grammar#0))), c#2)): DatatypeType))))));

procedure CheckWellformed$$TestModule8.__default.ValInGrammar(val#0: DatatypeType where $Is(val#0, Tclass.TestModule8.V()), 
    grammar#0: DatatypeType where $Is(grammar#0, Tclass.TestModule8.G()));
  free requires 4 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.__default.ValInGrammar(val#0: DatatypeType, grammar#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var _mcc#2#0: int;
  var _mcc#3#0: DatatypeType;
  var val#Z#0: DatatypeType;
  var let#0#0#0: DatatypeType;
  var c#Z#0: int;
  var let#1#0#0: int;
  var ##val#0: DatatypeType;
  var ##grammar#0: DatatypeType;
  var _mcc#1#0: Seq Box;
  var t#Z#0: Seq Box;
  var let#2#0#0: Seq Box;
  var i#4: int;
  var ##val#1: DatatypeType;
  var ##grammar#1: DatatypeType;
  var _mcc#0#0: int;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function ValInGrammar
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(308,28): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_TestModule8._default.ValInGrammar
       == $LS($LS(BaseFuel_TestModule8._default.ValInGrammar));
    assume StartFuelAssert_TestModule8._default.ValInGrammar
       == $LS($LS($LS(BaseFuel_TestModule8._default.ValInGrammar)));
    assume AsFuelBottom(BaseFuel_TestModule8._default.ValInGrammar)
       == BaseFuel_TestModule8._default.ValInGrammar;
    if (*)
    {
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        if (val#0 == #TestModule8.V.VUint64(_mcc#0#0))
        {
            assume LitInt(0) <= _mcc#0#0 && _mcc#0#0 < 18446744073709551616;
            assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, val#0, grammar#0)
               == TestModule8.G.GUint64_q(grammar#0);
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, val#0, grammar#0), 
              TBool);
        }
        else if (val#0 == #TestModule8.V.VTuple(_mcc#1#0))
        {
            assume $Is(_mcc#1#0, TSeq(Tclass.TestModule8.V()));
            havoc t#Z#0;
            assume $Is(t#Z#0, TSeq(Tclass.TestModule8.V()));
            assume let#2#0#0 == _mcc#1#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#2#0#0, TSeq(Tclass.TestModule8.V()));
            assume t#Z#0 == let#2#0#0;
            if (TestModule8.G.GTuple_q(grammar#0))
            {
                assert TestModule8.G.GTuple_q(grammar#0);
            }

            if (TestModule8.G.GTuple_q(grammar#0)
               && Seq#Length(t#Z#0) == Seq#Length(TestModule8.G.t(grammar#0)))
            {
                // Begin Comprehension WF check
                havoc i#4;
                if (true)
                {
                    if (LitInt(0) <= i#4)
                    {
                    }

                    if (LitInt(0) <= i#4 && i#4 < Seq#Length(t#Z#0))
                    {
                        assert 0 <= i#4 && i#4 < Seq#Length(t#Z#0);
                        assert TestModule8.G.GTuple_q(grammar#0);
                        assert 0 <= i#4 && i#4 < Seq#Length(TestModule8.G.t(grammar#0));
                        ##val#1 := $Unbox(Seq#Index(t#Z#0, i#4)): DatatypeType;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##val#1, Tclass.TestModule8.V(), $Heap);
                        ##grammar#1 := $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#4)): DatatypeType;
                        // assume allocatedness for argument to function
                        assume $IsAlloc(##grammar#1, Tclass.TestModule8.G(), $Heap);
                        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                        assert DtRank(##val#1) < DtRank(val#0)
                           || (DtRank(##val#1) == DtRank(val#0) && DtRank(##grammar#1) < DtRank(grammar#0));
                        assume TestModule8.__default.ValInGrammar#canCall($Unbox(Seq#Index(t#Z#0, i#4)): DatatypeType, 
                          $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#4)): DatatypeType);
                    }
                }

                // End Comprehension WF check
            }

            assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, val#0, grammar#0)
               == (
                TestModule8.G.GTuple_q(grammar#0)
                 && Seq#Length(t#Z#0) == Seq#Length(TestModule8.G.t(grammar#0))
                 && (forall i#5: int :: 
                  { $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#5)): DatatypeType } 
                    { $Unbox(Seq#Index(t#Z#0, i#5)): DatatypeType } 
                  true
                     ==> 
                    LitInt(0) <= i#5 && i#5 < Seq#Length(t#Z#0)
                     ==> TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
                      $Unbox(Seq#Index(t#Z#0, i#5)): DatatypeType, 
                      $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#5)): DatatypeType)));
            assume TestModule8.G.GTuple_q(grammar#0)
               ==> 
              Seq#Length(t#Z#0) == Seq#Length(TestModule8.G.t(grammar#0))
               ==> (forall i#5: int :: 
                { $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#5)): DatatypeType } 
                  { $Unbox(Seq#Index(t#Z#0, i#5)): DatatypeType } 
                LitInt(0) <= i#5
                   ==> 
                  i#5 < Seq#Length(t#Z#0)
                   ==> TestModule8.__default.ValInGrammar#canCall($Unbox(Seq#Index(t#Z#0, i#5)): DatatypeType, 
                    $Unbox(Seq#Index(TestModule8.G.t(grammar#0), i#5)): DatatypeType));
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, val#0, grammar#0), 
              TBool);
        }
        else if (val#0 == #TestModule8.V.VCase(_mcc#2#0, _mcc#3#0))
        {
            assume LitInt(0) <= _mcc#2#0 && _mcc#2#0 < 18446744073709551616;
            assume $Is(_mcc#3#0, Tclass.TestModule8.V());
            havoc val#Z#0;
            assume $Is(val#Z#0, Tclass.TestModule8.V());
            assume let#0#0#0 == _mcc#3#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#0#0#0, Tclass.TestModule8.V());
            assume val#Z#0 == let#0#0#0;
            havoc c#Z#0;
            assume LitInt(0) <= c#Z#0 && c#Z#0 < 18446744073709551616;
            assume let#1#0#0 == _mcc#2#0;
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(let#1#0#0, Tclass.TestModule8.uint64());
            assume c#Z#0 == let#1#0#0;
            if (TestModule8.G.GTaggedUnion_q(grammar#0))
            {
                assert TestModule8.G.GTaggedUnion_q(grammar#0);
            }

            if (TestModule8.G.GTaggedUnion_q(grammar#0)
               && c#Z#0 < Seq#Length(TestModule8.G.cases(grammar#0)))
            {
                assert TestModule8.G.GTaggedUnion_q(grammar#0);
                assert 0 <= c#Z#0 && c#Z#0 < Seq#Length(TestModule8.G.cases(grammar#0));
                ##val#0 := val#Z#0;
                // assume allocatedness for argument to function
                assume $IsAlloc(##val#0, Tclass.TestModule8.V(), $Heap);
                ##grammar#0 := $Unbox(Seq#Index(TestModule8.G.cases(grammar#0), c#Z#0)): DatatypeType;
                // assume allocatedness for argument to function
                assume $IsAlloc(##grammar#0, Tclass.TestModule8.G(), $Heap);
                b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
                assert DtRank(##val#0) < DtRank(val#0)
                   || (DtRank(##val#0) == DtRank(val#0) && DtRank(##grammar#0) < DtRank(grammar#0));
                assume TestModule8.__default.ValInGrammar#canCall(val#Z#0, $Unbox(Seq#Index(TestModule8.G.cases(grammar#0), c#Z#0)): DatatypeType);
            }

            assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, val#0, grammar#0)
               == (
                TestModule8.G.GTaggedUnion_q(grammar#0)
                 && c#Z#0 < Seq#Length(TestModule8.G.cases(grammar#0))
                 && TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
                  val#Z#0, 
                  $Unbox(Seq#Index(TestModule8.G.cases(grammar#0), c#Z#0)): DatatypeType));
            assume TestModule8.G.GTaggedUnion_q(grammar#0)
               ==> 
              c#Z#0 < Seq#Length(TestModule8.G.cases(grammar#0))
               ==> TestModule8.__default.ValInGrammar#canCall(val#Z#0, $Unbox(Seq#Index(TestModule8.G.cases(grammar#0), c#Z#0)): DatatypeType);
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, val#0, grammar#0), 
              TBool);
        }
        else
        {
            assume false;
        }

        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for TestModule8._default.EndPoint_grammar
function TestModule8.__default.EndPoint__grammar() : DatatypeType;

function TestModule8.__default.EndPoint__grammar#canCall() : bool;

// consequence axiom for TestModule8.__default.EndPoint__grammar
axiom 5 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.EndPoint__grammar#canCall() || 5 != $FunctionContextHeight
   ==> $Is(TestModule8.__default.EndPoint__grammar(), Tclass.TestModule8.G());

function TestModule8.__default.EndPoint__grammar#requires() : bool;

// #requires axiom for TestModule8.__default.EndPoint__grammar
axiom TestModule8.__default.EndPoint__grammar#requires() == true;

// definition axiom for TestModule8.__default.EndPoint__grammar (revealed)
axiom 5 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.EndPoint__grammar#canCall() || 5 != $FunctionContextHeight
   ==> TestModule8.__default.EndPoint__grammar() == Lit(#TestModule8.G.GUint64());

// definition axiom for TestModule8.__default.EndPoint__grammar for all literals (revealed)
axiom 5 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.EndPoint__grammar#canCall() || 5 != $FunctionContextHeight
   ==> TestModule8.__default.EndPoint__grammar() == Lit(#TestModule8.G.GUint64());

procedure CheckWellformed$$TestModule8.__default.EndPoint__grammar();
  free requires 5 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for TestModule8._default.CRequest_grammar
function TestModule8.__default.CRequest__grammar() : DatatypeType;

function TestModule8.__default.CRequest__grammar#canCall() : bool;

// consequence axiom for TestModule8.__default.CRequest__grammar
axiom 7 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.CRequest__grammar#canCall() || 7 != $FunctionContextHeight
   ==> $Is(TestModule8.__default.CRequest__grammar(), Tclass.TestModule8.G());

function TestModule8.__default.CRequest__grammar#requires() : bool;

// #requires axiom for TestModule8.__default.CRequest__grammar
axiom TestModule8.__default.CRequest__grammar#requires() == true;

// definition axiom for TestModule8.__default.CRequest__grammar (revealed)
axiom 7 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.CRequest__grammar#canCall() || 7 != $FunctionContextHeight
   ==> TestModule8.__default.EndPoint__grammar#canCall()
     && TestModule8.__default.CAppMessage__grammar#canCall()
     && TestModule8.__default.CRequest__grammar()
       == Lit(#TestModule8.G.GTaggedUnion(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, 
                $Box(Lit(#TestModule8.G.GTuple(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(Lit(TestModule8.__default.EndPoint__grammar()))), 
                            $Box(Lit(#TestModule8.G.GUint64()))), 
                          $Box(Lit(TestModule8.__default.CAppMessage__grammar())))))))), 
              $Box(Lit(#TestModule8.G.GUint64()))))));

// definition axiom for TestModule8.__default.CRequest__grammar for all literals (revealed)
axiom 7 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.CRequest__grammar#canCall() || 7 != $FunctionContextHeight
   ==> TestModule8.__default.EndPoint__grammar#canCall()
     && TestModule8.__default.CAppMessage__grammar#canCall()
     && TestModule8.__default.CRequest__grammar()
       == Lit(#TestModule8.G.GTaggedUnion(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, 
                $Box(Lit(#TestModule8.G.GTuple(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(Lit(TestModule8.__default.EndPoint__grammar()))), 
                            $Box(Lit(#TestModule8.G.GUint64()))), 
                          $Box(Lit(TestModule8.__default.CAppMessage__grammar())))))))), 
              $Box(Lit(#TestModule8.G.GUint64()))))));

procedure CheckWellformed$$TestModule8.__default.CRequest__grammar();
  free requires 7 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.__default.CRequest__grammar()
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function CRequest_grammar
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(321,24): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_TestModule8._default.ValInGrammar
       == $LS($LS(BaseFuel_TestModule8._default.ValInGrammar));
    assume StartFuelAssert_TestModule8._default.ValInGrammar
       == $LS($LS($LS(BaseFuel_TestModule8._default.ValInGrammar)));
    assume AsFuelBottom(BaseFuel_TestModule8._default.ValInGrammar)
       == BaseFuel_TestModule8._default.ValInGrammar;
    if (*)
    {
        assume $Is(TestModule8.__default.CRequest__grammar(), Tclass.TestModule8.G());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume TestModule8.__default.EndPoint__grammar#canCall();
        b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
        assume TestModule8.__default.CAppMessage__grammar#canCall();
        assume TestModule8.__default.CRequest__grammar()
           == Lit(#TestModule8.G.GTaggedUnion(Lit(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, 
                    $Box(Lit(#TestModule8.G.GTuple(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(Lit(TestModule8.__default.EndPoint__grammar()))), 
                                $Box(Lit(#TestModule8.G.GUint64()))), 
                              $Box(Lit(TestModule8.__default.CAppMessage__grammar())))))))), 
                  $Box(Lit(#TestModule8.G.GUint64()))))));
        assume TestModule8.__default.EndPoint__grammar#canCall()
           && TestModule8.__default.CAppMessage__grammar#canCall();
        // CheckWellformedWithResult: any expression
        assume $Is(TestModule8.__default.CRequest__grammar(), Tclass.TestModule8.G());
        assert b$reqreads#0;
        assert b$reqreads#1;
    }
}



// function declaration for TestModule8._default.parse_EndPoint
function TestModule8.__default.parse__EndPoint(val#0: DatatypeType) : Box;

function TestModule8.__default.parse__EndPoint#canCall(val#0: DatatypeType) : bool;

// consequence axiom for TestModule8.__default.parse__EndPoint
axiom 8 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    { TestModule8.__default.parse__EndPoint(val#0) } 
    TestModule8.__default.parse__EndPoint#canCall(val#0)
         || (8 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
            val#0, 
            Lit(TestModule8.__default.EndPoint__grammar())))
       ==> $IsBox(TestModule8.__default.parse__EndPoint(val#0), #$EndPoint));

function TestModule8.__default.parse__EndPoint#requires(DatatypeType) : bool;

// #requires axiom for TestModule8.__default.parse__EndPoint
axiom (forall val#0: DatatypeType :: 
  { TestModule8.__default.parse__EndPoint#requires(val#0) } 
  $Is(val#0, Tclass.TestModule8.V())
     ==> TestModule8.__default.parse__EndPoint#requires(val#0)
       == TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
        val#0, 
        Lit(TestModule8.__default.EndPoint__grammar())));

procedure CheckWellformed$$TestModule8.__default.parse__EndPoint(val#0: DatatypeType where $Is(val#0, Tclass.TestModule8.V()));
  free requires 8 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.__default.parse__EndPoint(val#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##val#0: DatatypeType;
  var ##grammar#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function parse_EndPoint
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(323,24): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_TestModule8._default.ValInGrammar
       == $LS($LS(BaseFuel_TestModule8._default.ValInGrammar));
    assume StartFuelAssert_TestModule8._default.ValInGrammar
       == $LS($LS($LS(BaseFuel_TestModule8._default.ValInGrammar)));
    assume AsFuelBottom(BaseFuel_TestModule8._default.ValInGrammar)
       == BaseFuel_TestModule8._default.ValInGrammar;
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.EndPoint__grammar#canCall();
    ##val#0 := val#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##val#0, Tclass.TestModule8.V(), $Heap);
    ##grammar#0 := Lit(TestModule8.__default.EndPoint__grammar());
    // assume allocatedness for argument to function
    assume $IsAlloc(##grammar#0, Tclass.TestModule8.G(), $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.ValInGrammar#canCall(val#0, Lit(TestModule8.__default.EndPoint__grammar()));
    assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
      val#0, 
      Lit(TestModule8.__default.EndPoint__grammar()));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $IsBox(TestModule8.__default.parse__EndPoint(val#0), #$EndPoint);
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for TestModule8._default.CAppMessage_grammar
function TestModule8.__default.CAppMessage__grammar() : DatatypeType;

function TestModule8.__default.CAppMessage__grammar#canCall() : bool;

// consequence axiom for TestModule8.__default.CAppMessage__grammar
axiom 6 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.CAppMessage__grammar#canCall()
     || 6 != $FunctionContextHeight
   ==> $Is(TestModule8.__default.CAppMessage__grammar(), Tclass.TestModule8.G());

function TestModule8.__default.CAppMessage__grammar#requires() : bool;

// #requires axiom for TestModule8.__default.CAppMessage__grammar
axiom TestModule8.__default.CAppMessage__grammar#requires() == true;

// definition axiom for TestModule8.__default.CAppMessage__grammar (revealed)
axiom 6 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.CAppMessage__grammar#canCall()
     || 6 != $FunctionContextHeight
   ==> TestModule8.__default.CAppMessage__grammar()
     == Lit(#TestModule8.G.GTaggedUnion(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(Lit(#TestModule8.G.GUint64()))), 
              $Box(Lit(#TestModule8.G.GUint64()))), 
            $Box(Lit(#TestModule8.G.GUint64()))))));

// definition axiom for TestModule8.__default.CAppMessage__grammar for all literals (revealed)
axiom 6 <= $FunctionContextHeight
   ==> 
  TestModule8.__default.CAppMessage__grammar#canCall()
     || 6 != $FunctionContextHeight
   ==> TestModule8.__default.CAppMessage__grammar()
     == Lit(#TestModule8.G.GTaggedUnion(Lit(Seq#Build(Seq#Build(Seq#Build(Seq#Empty(): Seq Box, $Box(Lit(#TestModule8.G.GUint64()))), 
              $Box(Lit(#TestModule8.G.GUint64()))), 
            $Box(Lit(#TestModule8.G.GUint64()))))));

procedure CheckWellformed$$TestModule8.__default.CAppMessage__grammar();
  free requires 6 == $FunctionContextHeight;
  modifies $Heap, $Tick;



// function declaration for TestModule8._default.parse_AppMessage
function TestModule8.__default.parse__AppMessage(val#0: DatatypeType) : Box;

function TestModule8.__default.parse__AppMessage#canCall(val#0: DatatypeType) : bool;

// consequence axiom for TestModule8.__default.parse__AppMessage
axiom 9 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    { TestModule8.__default.parse__AppMessage(val#0) } 
    TestModule8.__default.parse__AppMessage#canCall(val#0)
         || (9 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
            val#0, 
            Lit(TestModule8.__default.CAppMessage__grammar())))
       ==> $IsBox(TestModule8.__default.parse__AppMessage(val#0), #$CAppMessage));

function TestModule8.__default.parse__AppMessage#requires(DatatypeType) : bool;

// #requires axiom for TestModule8.__default.parse__AppMessage
axiom (forall val#0: DatatypeType :: 
  { TestModule8.__default.parse__AppMessage#requires(val#0) } 
  $Is(val#0, Tclass.TestModule8.V())
     ==> TestModule8.__default.parse__AppMessage#requires(val#0)
       == TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
        val#0, 
        Lit(TestModule8.__default.CAppMessage__grammar())));

procedure CheckWellformed$$TestModule8.__default.parse__AppMessage(val#0: DatatypeType where $Is(val#0, Tclass.TestModule8.V()));
  free requires 9 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.__default.parse__AppMessage(val#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##val#0: DatatypeType;
  var ##grammar#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;

    // AddWellformednessCheck for function parse_AppMessage
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(328,24): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_TestModule8._default.ValInGrammar
       == $LS($LS(BaseFuel_TestModule8._default.ValInGrammar));
    assume StartFuelAssert_TestModule8._default.ValInGrammar
       == $LS($LS($LS(BaseFuel_TestModule8._default.ValInGrammar)));
    assume AsFuelBottom(BaseFuel_TestModule8._default.ValInGrammar)
       == BaseFuel_TestModule8._default.ValInGrammar;
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.CAppMessage__grammar#canCall();
    ##val#0 := val#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##val#0, Tclass.TestModule8.V(), $Heap);
    ##grammar#0 := Lit(TestModule8.__default.CAppMessage__grammar());
    // assume allocatedness for argument to function
    assume $IsAlloc(##grammar#0, Tclass.TestModule8.G(), $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.ValInGrammar#canCall(val#0, Lit(TestModule8.__default.CAppMessage__grammar()));
    assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
      val#0, 
      Lit(TestModule8.__default.CAppMessage__grammar()));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $IsBox(TestModule8.__default.parse__AppMessage(val#0), #$CAppMessage);
        assume false;
    }
    else
    {
        assume false;
    }
}



// function declaration for TestModule8._default.parse_Request1
function TestModule8.__default.parse__Request1(val#0: DatatypeType) : DatatypeType;

function TestModule8.__default.parse__Request1#canCall(val#0: DatatypeType) : bool;

// consequence axiom for TestModule8.__default.parse__Request1
axiom 10 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    { TestModule8.__default.parse__Request1(val#0) } 
    TestModule8.__default.parse__Request1#canCall(val#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && TestModule8.__default.ValInGrammar(StartFuel_TestModule8._default.ValInGrammar, 
            val#0, 
            Lit(TestModule8.__default.CRequest__grammar())))
       ==> $Is(TestModule8.__default.parse__Request1(val#0), Tclass.TestModule8.CRequest()));

function TestModule8.__default.parse__Request1#requires(DatatypeType) : bool;

// #requires axiom for TestModule8.__default.parse__Request1
axiom (forall val#0: DatatypeType :: 
  { TestModule8.__default.parse__Request1#requires(val#0) } 
  $Is(val#0, Tclass.TestModule8.V())
     ==> TestModule8.__default.parse__Request1#requires(val#0)
       == TestModule8.__default.ValInGrammar(StartFuel_TestModule8._default.ValInGrammar, 
        val#0, 
        Lit(TestModule8.__default.CRequest__grammar())));

// definition axiom for TestModule8.__default.parse__Request1 (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    { TestModule8.__default.parse__Request1(val#0) } 
    TestModule8.__default.parse__Request1#canCall(val#0)
         || (10 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && TestModule8.__default.ValInGrammar(StartFuel_TestModule8._default.ValInGrammar, 
            val#0, 
            Lit(TestModule8.__default.CRequest__grammar())))
       ==> (TestModule8.V.c(val#0) == LitInt(0)
           ==> TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType)
             && TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType))
         && TestModule8.__default.parse__Request1(val#0)
           == (if TestModule8.V.c(val#0) == LitInt(0)
             then (var ep#0 := TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType); 
              #TestModule8.CRequest.CRequest(ep#0, 
                TestModule8.V.u($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType)))
             else #TestModule8.CRequest.CRequestNoOp()));

// definition axiom for TestModule8.__default.parse__Request1 for all literals (revealed)
axiom 10 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    {:weight 3} { TestModule8.__default.parse__Request1(Lit(val#0)) } 
    TestModule8.__default.parse__Request1#canCall(Lit(val#0))
         || (10 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && Lit(TestModule8.__default.ValInGrammar(StartFuel_TestModule8._default.ValInGrammar, 
              Lit(val#0), 
              Lit(TestModule8.__default.CRequest__grammar()))))
       ==> (LitInt(TestModule8.V.c(Lit(val#0))) == LitInt(0)
           ==> TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(0))): DatatypeType)
             && TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(2))): DatatypeType))
         && TestModule8.__default.parse__Request1(Lit(val#0))
           == (if LitInt(TestModule8.V.c(Lit(val#0))) == LitInt(0)
             then (var ep#1 := TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(0))): DatatypeType); 
              #TestModule8.CRequest.CRequest(ep#1, 
                TestModule8.V.u($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(2))): DatatypeType)))
             else #TestModule8.CRequest.CRequestNoOp()));

procedure CheckWellformed$$TestModule8.__default.parse__Request1(val#0: DatatypeType where $Is(val#0, Tclass.TestModule8.V()));
  free requires 10 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.__default.parse__Request1(val#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##val#0: DatatypeType;
  var ##grammar#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var newtype$check#0: int;
  var ep#Z#0: Box;
  var let#0#0#0: Box;
  var ##val#1: DatatypeType;
  var ##val#2: DatatypeType;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function parse_Request1
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(331,47): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_TestModule8._default.ValInGrammar
       == $LS(BaseFuel_TestModule8._default.ValInGrammar);
    assume StartFuelAssert_TestModule8._default.ValInGrammar
       == $LS($LS(BaseFuel_TestModule8._default.ValInGrammar));
    assume AsFuelBottom(BaseFuel_TestModule8._default.ValInGrammar)
       == BaseFuel_TestModule8._default.ValInGrammar;
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.CRequest__grammar#canCall();
    ##val#0 := val#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##val#0, Tclass.TestModule8.V(), $Heap);
    ##grammar#0 := Lit(TestModule8.__default.CRequest__grammar());
    // assume allocatedness for argument to function
    assume $IsAlloc(##grammar#0, Tclass.TestModule8.G(), $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.ValInGrammar#canCall(val#0, Lit(TestModule8.__default.CRequest__grammar()));
    assume TestModule8.__default.ValInGrammar(StartFuel_TestModule8._default.ValInGrammar, 
      val#0, 
      Lit(TestModule8.__default.CRequest__grammar()));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $Is(TestModule8.__default.parse__Request1(val#0), Tclass.TestModule8.CRequest());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert TestModule8.V.VCase_q(val#0);
        newtype$check#0 := LitInt(0);
        assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 18446744073709551616;
        if (TestModule8.V.c(val#0) == LitInt(0))
        {
            havoc ep#Z#0;
            assume $IsBox(ep#Z#0, #$EndPoint);
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(0)
               && LitInt(0) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            ##val#1 := $Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#1, Tclass.TestModule8.V(), $Heap);
            assert {:subsumption 0} TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#1, 
              Lit(TestModule8.__default.EndPoint__grammar()));
            assume TestModule8.__default.ValInGrammar(StartFuel_TestModule8._default.ValInGrammar, 
              ##val#1, 
              Lit(TestModule8.__default.EndPoint__grammar()));
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            assume let#0#0#0
               == TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            assume TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0#0#0, #$EndPoint);
            assume ep#Z#0 == let#0#0#0;
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(1)
               && LitInt(1) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            assert TestModule8.V.VUint64_q($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType);
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(2)
               && LitInt(2) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            ##val#2 := $Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#2, Tclass.TestModule8.V(), $Heap);
            assert {:subsumption 0} TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#2, 
              Lit(TestModule8.__default.CAppMessage__grammar()));
            assume TestModule8.__default.ValInGrammar(StartFuel_TestModule8._default.ValInGrammar, 
              ##val#2, 
              Lit(TestModule8.__default.CAppMessage__grammar()));
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType);
            assume TestModule8.__default.parse__Request1(val#0)
               == #TestModule8.CRequest.CRequest(ep#Z#0, 
                TestModule8.V.u($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType));
            assume TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType);
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.parse__Request1(val#0), Tclass.TestModule8.CRequest());
        }
        else
        {
            assume TestModule8.__default.parse__Request1(val#0)
               == Lit(#TestModule8.CRequest.CRequestNoOp());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.parse__Request1(val#0), Tclass.TestModule8.CRequest());
        }

        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for TestModule8._default.parse_Request2
function TestModule8.__default.parse__Request2(val#0: DatatypeType) : DatatypeType;

function TestModule8.__default.parse__Request2#canCall(val#0: DatatypeType) : bool;

// consequence axiom for TestModule8.__default.parse__Request2
axiom 11 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    { TestModule8.__default.parse__Request2(val#0) } 
    TestModule8.__default.parse__Request2#canCall(val#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
            val#0, 
            Lit(TestModule8.__default.CRequest__grammar())))
       ==> $Is(TestModule8.__default.parse__Request2(val#0), Tclass.TestModule8.CRequest()));

function TestModule8.__default.parse__Request2#requires(DatatypeType) : bool;

// #requires axiom for TestModule8.__default.parse__Request2
axiom (forall val#0: DatatypeType :: 
  { TestModule8.__default.parse__Request2#requires(val#0) } 
  $Is(val#0, Tclass.TestModule8.V())
     ==> TestModule8.__default.parse__Request2#requires(val#0)
       == TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
        val#0, 
        Lit(TestModule8.__default.CRequest__grammar())));

// definition axiom for TestModule8.__default.parse__Request2 (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    { TestModule8.__default.parse__Request2(val#0) } 
    TestModule8.__default.parse__Request2#canCall(val#0)
         || (11 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
            val#0, 
            Lit(TestModule8.__default.CRequest__grammar())))
       ==> (TestModule8.V.c(val#0) == LitInt(0)
           ==> TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType)
             && TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType))
         && TestModule8.__default.parse__Request2(val#0)
           == (if TestModule8.V.c(val#0) == LitInt(0)
             then (var ep#0 := TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType); 
              #TestModule8.CRequest.CRequest(ep#0, 
                TestModule8.V.u($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType)))
             else #TestModule8.CRequest.CRequestNoOp()));

// definition axiom for TestModule8.__default.parse__Request2 for all literals (revealed)
axiom 11 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    {:weight 3} { TestModule8.__default.parse__Request2(Lit(val#0)) } 
    TestModule8.__default.parse__Request2#canCall(Lit(val#0))
         || (11 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && Lit(TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              Lit(val#0), 
              Lit(TestModule8.__default.CRequest__grammar()))))
       ==> (LitInt(TestModule8.V.c(Lit(val#0))) == LitInt(0)
           ==> TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(0))): DatatypeType)
             && TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(2))): DatatypeType))
         && TestModule8.__default.parse__Request2(Lit(val#0))
           == (if LitInt(TestModule8.V.c(Lit(val#0))) == LitInt(0)
             then (var ep#1 := TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(0))): DatatypeType); 
              #TestModule8.CRequest.CRequest(ep#1, 
                TestModule8.V.u($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(2))): DatatypeType)))
             else #TestModule8.CRequest.CRequestNoOp()));

procedure CheckWellformed$$TestModule8.__default.parse__Request2(val#0: DatatypeType where $Is(val#0, Tclass.TestModule8.V()));
  free requires 11 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.__default.parse__Request2(val#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##val#0: DatatypeType;
  var ##grammar#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var newtype$check#0: int;
  var ep#Z#0: Box;
  var let#0#0#0: Box;
  var ##val#1: DatatypeType;
  var ##val#2: DatatypeType;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function parse_Request2
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(341,24): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_TestModule8._default.ValInGrammar
       == $LS($LS(BaseFuel_TestModule8._default.ValInGrammar));
    assume StartFuelAssert_TestModule8._default.ValInGrammar
       == $LS($LS($LS(BaseFuel_TestModule8._default.ValInGrammar)));
    assume AsFuelBottom(BaseFuel_TestModule8._default.ValInGrammar)
       == BaseFuel_TestModule8._default.ValInGrammar;
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.CRequest__grammar#canCall();
    ##val#0 := val#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##val#0, Tclass.TestModule8.V(), $Heap);
    ##grammar#0 := Lit(TestModule8.__default.CRequest__grammar());
    // assume allocatedness for argument to function
    assume $IsAlloc(##grammar#0, Tclass.TestModule8.G(), $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.ValInGrammar#canCall(val#0, Lit(TestModule8.__default.CRequest__grammar()));
    assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
      val#0, 
      Lit(TestModule8.__default.CRequest__grammar()));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $Is(TestModule8.__default.parse__Request2(val#0), Tclass.TestModule8.CRequest());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert TestModule8.V.VCase_q(val#0);
        newtype$check#0 := LitInt(0);
        assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 18446744073709551616;
        if (TestModule8.V.c(val#0) == LitInt(0))
        {
            havoc ep#Z#0;
            assume $IsBox(ep#Z#0, #$EndPoint);
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(0)
               && LitInt(0) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            ##val#1 := $Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#1, Tclass.TestModule8.V(), $Heap);
            assert {:subsumption 0} TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#1, 
              Lit(TestModule8.__default.EndPoint__grammar()));
            assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#1, 
              Lit(TestModule8.__default.EndPoint__grammar()));
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            assume let#0#0#0
               == TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            assume TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0#0#0, #$EndPoint);
            assume ep#Z#0 == let#0#0#0;
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(1)
               && LitInt(1) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            assert TestModule8.V.VUint64_q($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType);
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(2)
               && LitInt(2) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            ##val#2 := $Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#2, Tclass.TestModule8.V(), $Heap);
            assert {:subsumption 0} TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#2, 
              Lit(TestModule8.__default.CAppMessage__grammar()));
            assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#2, 
              Lit(TestModule8.__default.CAppMessage__grammar()));
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType);
            assume TestModule8.__default.parse__Request2(val#0)
               == #TestModule8.CRequest.CRequest(ep#Z#0, 
                TestModule8.V.u($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType));
            assume TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType);
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.parse__Request2(val#0), Tclass.TestModule8.CRequest());
        }
        else
        {
            assume TestModule8.__default.parse__Request2(val#0)
               == Lit(#TestModule8.CRequest.CRequestNoOp());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.parse__Request2(val#0), Tclass.TestModule8.CRequest());
        }

        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



// function declaration for TestModule8._default.parse_Request3
function TestModule8.__default.parse__Request3(val#0: DatatypeType) : DatatypeType;

function TestModule8.__default.parse__Request3#canCall(val#0: DatatypeType) : bool;

// consequence axiom for TestModule8.__default.parse__Request3
axiom 12 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    { TestModule8.__default.parse__Request3(val#0) } 
    TestModule8.__default.parse__Request3#canCall(val#0)
         || (12 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
            val#0, 
            Lit(TestModule8.__default.CRequest__grammar())))
       ==> $Is(TestModule8.__default.parse__Request3(val#0), Tclass.TestModule8.CRequest()));

function TestModule8.__default.parse__Request3#requires(DatatypeType) : bool;

// #requires axiom for TestModule8.__default.parse__Request3
axiom (forall val#0: DatatypeType :: 
  { TestModule8.__default.parse__Request3#requires(val#0) } 
  $Is(val#0, Tclass.TestModule8.V())
     ==> TestModule8.__default.parse__Request3#requires(val#0)
       == TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
        val#0, 
        Lit(TestModule8.__default.CRequest__grammar())));

// definition axiom for TestModule8.__default.parse__Request3 (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    { TestModule8.__default.parse__Request3(val#0) } 
    TestModule8.__default.parse__Request3#canCall(val#0)
         || (12 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
            val#0, 
            Lit(TestModule8.__default.CRequest__grammar())))
       ==> (TestModule8.V.c(val#0) == LitInt(0)
           ==> TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType)
             && TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType))
         && TestModule8.__default.parse__Request3(val#0)
           == (if TestModule8.V.c(val#0) == LitInt(0)
             then (var ep#0 := TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType); 
              #TestModule8.CRequest.CRequest(ep#0, 
                TestModule8.V.u($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType)))
             else #TestModule8.CRequest.CRequestNoOp()));

// definition axiom for TestModule8.__default.parse__Request3 for all literals (revealed)
axiom 12 <= $FunctionContextHeight
   ==> (forall val#0: DatatypeType :: 
    {:weight 3} { TestModule8.__default.parse__Request3(Lit(val#0)) } 
    TestModule8.__default.parse__Request3#canCall(Lit(val#0))
         || (12 != $FunctionContextHeight
           && 
          $Is(val#0, Tclass.TestModule8.V())
           && Lit(TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              Lit(val#0), 
              Lit(TestModule8.__default.CRequest__grammar()))))
       ==> (LitInt(TestModule8.V.c(Lit(val#0))) == LitInt(0)
           ==> TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(0))): DatatypeType)
             && TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(2))): DatatypeType))
         && TestModule8.__default.parse__Request3(Lit(val#0))
           == (if LitInt(TestModule8.V.c(Lit(val#0))) == LitInt(0)
             then (var ep#1 := TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(0))): DatatypeType); 
              #TestModule8.CRequest.CRequest(ep#1, 
                TestModule8.V.u($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(Lit(TestModule8.V.t(Lit(TestModule8.V.val(Lit(val#0))))), LitInt(2))): DatatypeType)))
             else #TestModule8.CRequest.CRequestNoOp()));

procedure CheckWellformed$$TestModule8.__default.parse__Request3(val#0: DatatypeType where $Is(val#0, Tclass.TestModule8.V()));
  free requires 12 == $FunctionContextHeight;
  modifies $Heap, $Tick;



implementation CheckWellformed$$TestModule8.__default.parse__Request3(val#0: DatatypeType)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var ##val#0: DatatypeType;
  var ##grammar#0: DatatypeType;
  var b$reqreads#0: bool;
  var b$reqreads#1: bool;
  var newtype$check#0: int;
  var ep#Z#0: Box;
  var let#0#0#0: Box;
  var ##val#1: DatatypeType;
  var ##val#2: DatatypeType;
  var b$reqreads#2: bool;
  var b$reqreads#3: bool;

    b$reqreads#0 := true;
    b$reqreads#1 := true;
    b$reqreads#2 := true;
    b$reqreads#3 := true;

    // AddWellformednessCheck for function parse_Request3
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(351,47): initial state"} true;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    // initialize fuel constant
    assume StartFuel_TestModule8._default.ValInGrammar
       == $LS($LS($LS(BaseFuel_TestModule8._default.ValInGrammar)));
    assume StartFuelAssert_TestModule8._default.ValInGrammar
       == $LS($LS($LS($LS(BaseFuel_TestModule8._default.ValInGrammar))));
    assume AsFuelBottom(BaseFuel_TestModule8._default.ValInGrammar)
       == BaseFuel_TestModule8._default.ValInGrammar;
    b$reqreads#0 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.CRequest__grammar#canCall();
    ##val#0 := val#0;
    // assume allocatedness for argument to function
    assume $IsAlloc(##val#0, Tclass.TestModule8.V(), $Heap);
    ##grammar#0 := Lit(TestModule8.__default.CRequest__grammar());
    // assume allocatedness for argument to function
    assume $IsAlloc(##grammar#0, Tclass.TestModule8.G(), $Heap);
    b$reqreads#1 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    assume TestModule8.__default.ValInGrammar#canCall(val#0, Lit(TestModule8.__default.CRequest__grammar()));
    assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
      val#0, 
      Lit(TestModule8.__default.CRequest__grammar()));
    assert b$reqreads#0;
    assert b$reqreads#1;
    if (*)
    {
        assume $Is(TestModule8.__default.parse__Request3(val#0), Tclass.TestModule8.CRequest());
        assume false;
    }
    else
    {
        $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
          $o != null && read($Heap, $o, alloc) ==> false);
        assert TestModule8.V.VCase_q(val#0);
        newtype$check#0 := LitInt(0);
        assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 18446744073709551616;
        if (TestModule8.V.c(val#0) == LitInt(0))
        {
            havoc ep#Z#0;
            assume $IsBox(ep#Z#0, #$EndPoint);
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(0)
               && LitInt(0) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            ##val#1 := $Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#1, Tclass.TestModule8.V(), $Heap);
            assert {:subsumption 0} TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#1, 
              Lit(TestModule8.__default.EndPoint__grammar()));
            assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#1, 
              Lit(TestModule8.__default.EndPoint__grammar()));
            b$reqreads#2 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            assume let#0#0#0
               == TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            assume TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
            // CheckWellformedWithResult: any expression
            assume $IsBox(let#0#0#0, #$EndPoint);
            assume ep#Z#0 == let#0#0#0;
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(1)
               && LitInt(1) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            assert TestModule8.V.VUint64_q($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType);
            assert TestModule8.V.VCase_q(val#0);
            assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
            assert 0 <= LitInt(2)
               && LitInt(2) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
            ##val#2 := $Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType;
            // assume allocatedness for argument to function
            assume $IsAlloc(##val#2, Tclass.TestModule8.V(), $Heap);
            assert {:subsumption 0} TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#2, 
              Lit(TestModule8.__default.CAppMessage__grammar()));
            assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
              ##val#2, 
              Lit(TestModule8.__default.CAppMessage__grammar()));
            b$reqreads#3 := (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
            assume TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType);
            assume TestModule8.__default.parse__Request3(val#0)
               == #TestModule8.CRequest.CRequest(ep#Z#0, 
                TestModule8.V.u($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType), 
                TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType));
            assume TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType);
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.parse__Request3(val#0), Tclass.TestModule8.CRequest());
        }
        else
        {
            assume TestModule8.__default.parse__Request3(val#0)
               == Lit(#TestModule8.CRequest.CRequestNoOp());
            assume true;
            // CheckWellformedWithResult: any expression
            assume $Is(TestModule8.__default.parse__Request3(val#0), Tclass.TestModule8.CRequest());
        }

        assert b$reqreads#2;
        assert b$reqreads#3;
    }
}



procedure CheckWellformed$$TestModule8.__default.parse__Request4(val#0: DatatypeType
       where $Is(val#0, Tclass.TestModule8.V())
         && $IsAlloc(val#0, Tclass.TestModule8.V(), $Heap)
         && $IsA#TestModule8.V(val#0))
   returns (req#0: DatatypeType
       where $Is(req#0, Tclass.TestModule8.CRequest())
         && $IsAlloc(req#0, Tclass.TestModule8.CRequest(), $Heap));
  free requires 13 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$TestModule8.__default.parse__Request4(val#0: DatatypeType
       where $Is(val#0, Tclass.TestModule8.V())
         && $IsAlloc(val#0, Tclass.TestModule8.V(), $Heap)
         && $IsA#TestModule8.V(val#0))
   returns (req#0: DatatypeType
       where $Is(req#0, Tclass.TestModule8.CRequest())
         && $IsAlloc(req#0, Tclass.TestModule8.CRequest(), $Heap));
  // user-defined preconditions
  requires TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
    val#0, 
    Lit(TestModule8.__default.CRequest__grammar()));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$TestModule8.__default.parse__Request4(val#0: DatatypeType
       where $Is(val#0, Tclass.TestModule8.V())
         && $IsAlloc(val#0, Tclass.TestModule8.V(), $Heap)
         && $IsA#TestModule8.V(val#0))
   returns (req#0: DatatypeType
       where $Is(req#0, Tclass.TestModule8.CRequest())
         && $IsAlloc(req#0, Tclass.TestModule8.CRequest(), $Heap), 
    $_reverifyPost: bool);
  free requires 13 == $FunctionContextHeight;
  // user-defined preconditions
  requires TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
    val#0, 
    Lit(TestModule8.__default.CRequest__grammar()));
  modifies $Heap, $Tick;
  // frame condition: object granularity
  free ensures (forall $o: ref :: 
    { $Heap[$o] } 
    $o != null && read(old($Heap), $o, alloc) ==> $Heap[$o] == old($Heap)[$o]);
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$TestModule8.__default.parse__Request4(val#0: DatatypeType) returns (req#0: DatatypeType, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var newtype$check#0: int;
  var ep#0_0: Box
     where $IsBox(ep#0_0, #$EndPoint) && $IsAllocBox(ep#0_0, #$EndPoint, $Heap);
  var ##val#0_0: DatatypeType;
  var ##val#0_1: DatatypeType;

    // AddMethodImpl: parse_Request4, Impl$$TestModule8.__default.parse__Request4
    // initialize fuel constant
    assume StartFuel_TestModule8._default.ValInGrammar
       == $LS($LS(BaseFuel_TestModule8._default.ValInGrammar));
    assume StartFuelAssert_TestModule8._default.ValInGrammar
       == $LS($LS($LS(BaseFuel_TestModule8._default.ValInGrammar)));
    assume AsFuelBottom(BaseFuel_TestModule8._default.ValInGrammar)
       == BaseFuel_TestModule8._default.ValInGrammar;
    $_Frame := (lambda<alpha> $o: ref, $f: Field alpha :: 
      $o != null && read($Heap, $o, alloc) ==> false);
    assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(364,8): initial state"} true;
    $_reverifyPost := false;
    // ----- if statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(365,13)
    assert TestModule8.V.VCase_q(val#0);
    newtype$check#0 := LitInt(0);
    assert LitInt(0) <= newtype$check#0 && newtype$check#0 < 18446744073709551616;
    assume true;
    if (TestModule8.V.c(val#0) == LitInt(0))
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(366,24)
        assume true;
        assert TestModule8.V.VCase_q(val#0);
        assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
        assert 0 <= LitInt(0)
           && LitInt(0) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
        ##val#0_0 := $Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType;
        // assume allocatedness for argument to function
        assume $IsAlloc(##val#0_0, Tclass.TestModule8.V(), $Heap);
        assert {:subsumption 0} TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
          ##val#0_0, 
          Lit(TestModule8.__default.EndPoint__grammar()));
        assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
          ##val#0_0, 
          Lit(TestModule8.__default.EndPoint__grammar()));
        assume TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
        assume TestModule8.__default.parse__EndPoint#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
        ep#0_0 := TestModule8.__default.parse__EndPoint($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(0))): DatatypeType);
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(366,54)"} true;
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(367,21)
        assume true;
        assert TestModule8.V.VCase_q(val#0);
        assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
        assert 0 <= LitInt(1)
           && LitInt(1) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
        assert TestModule8.V.VUint64_q($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType);
        assert TestModule8.V.VCase_q(val#0);
        assert TestModule8.V.VTuple_q(TestModule8.V.val(val#0));
        assert 0 <= LitInt(2)
           && LitInt(2) < Seq#Length(TestModule8.V.t(TestModule8.V.val(val#0)));
        ##val#0_1 := $Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType;
        // assume allocatedness for argument to function
        assume $IsAlloc(##val#0_1, Tclass.TestModule8.V(), $Heap);
        assert {:subsumption 0} TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
          ##val#0_1, 
          Lit(TestModule8.__default.CAppMessage__grammar()));
        assume TestModule8.__default.ValInGrammar(StartFuelAssert_TestModule8._default.ValInGrammar, 
          ##val#0_1, 
          Lit(TestModule8.__default.CAppMessage__grammar()));
        assume TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType);
        assume TestModule8.__default.parse__AppMessage#canCall($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType);
        req#0 := #TestModule8.CRequest.CRequest(ep#0_0, 
          TestModule8.V.u($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(1))): DatatypeType), 
          TestModule8.__default.parse__AppMessage($Unbox(Seq#Index(TestModule8.V.t(TestModule8.V.val(val#0)), LitInt(2))): DatatypeType));
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(367,83)"} true;
    }
    else
    {
        // ----- assignment statement ----- /Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(369,21)
        assume true;
        assume true;
        req#0 := Lit(#TestModule8.CRequest.CRequestNoOp());
        assume {:captureState "/Users/jeffc/Desktop/boogie/Benchmarks/Dafny_ProgramCollection/dafny0/Fuel.dfy(369,37)"} true;
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

const unique tytagFamily$_tuple#0: TyTagFamily;

const unique tytagFamily$byte: TyTagFamily;

const unique tytagFamily$uint64: TyTagFamily;

const unique tytagFamily$G: TyTagFamily;

const unique tytagFamily$V: TyTagFamily;

const unique tytagFamily$CRequest: TyTagFamily;

const unique tytagFamily$_default: TyTagFamily;
